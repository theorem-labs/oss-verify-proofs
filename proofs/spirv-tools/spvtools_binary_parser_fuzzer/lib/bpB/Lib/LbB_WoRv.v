From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_Own LbB_ContStmt LbB_ContV4 LbB_DRep LbB_PrsStmt LbB_HStKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoKit3 LbB_WoSt LbB_WoVec LbB_WoCut.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_ResvB LbB_RvOC LbB_RvWC LbB_RvTC.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma fld_of_cellsR : forall m A cs k c v, rw_cells asegs m A cs -> cell_at cs k = Some c ->
  cbytes c = word_to_le_bytes (csize c) (Z_to_bv 64 v) -> fld ASEGS m (A + Z.of_nat k) (csize c) v.
Proof.
  intros m A cs k c v Hc Hk Hb. unfold fld.
  pose proof (rw_cells_read asegs m A cs k c Hc Hk) as RD. rewrite Hb in RD. rewrite <- rdn_of_ov. exact RD.
Qed.

Lemma z24_fld : forall m v o, rw_cells asegs m v [CB 24 (poison_bytes 24 0)] -> 0 <= o <= 16 -> fld ASEGS m (v + o) 8 0.
Proof.
  intros m v o Z Ho.
  pose proof (zero_cells_sub m v 24 o 8 Z ltac:(lia) ltac:(lia)) as Z8.
  pose proof (fld_of_cellsR m (v + o) [CB 8 (poison_bytes 8 0)] 0 (CB 8 (poison_bytes 8 0)) 0 Z8 eq_refl
                ltac:(vm_compute; reflexivity)) as F.
  rewrite Z.add_0_r in F. exact F.
Qed.

Lemma wrv_wr_sub : forall m A N, wr_at asegs m A N -> forall a n, A <= a -> a + n <= A + N -> wr_at asegs m a n.
Proof.
  intros m A N (W0 & W1 & W) a n X1 X2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + i) with (A + (a - A + i)) by lia. apply W. lia.
Qed.

Lemma wrv_trip : forall m v x y z, wr_at asegs m v 24 ->
  CRep.fld ASEGS m v 8 x -> CRep.fld ASEGS m (v + 8) 8 y -> CRep.fld ASEGS m (v + 16) 8 z ->
  rw_cells asegs m v [C8 (Z_to_bv 64 x); C8 (Z_to_bv 64 y); C8 (Z_to_bv 64 z)].
Proof.
  intros m v x y z W F1 F2 F3.
  pose proof (rw_cells_of_fld8 m v x F1 (wrv_wr_sub m v 24 W v 8 ltac:(lia) ltac:(lia))) as C1.
  pose proof (rw_cells_of_fld8 m (v + 8) y F2 (wrv_wr_sub m v 24 W (v + 8) 8 ltac:(lia) ltac:(lia))) as C2.
  pose proof (rw_cells_of_fld8 m (v + 16) z F3 (wrv_wr_sub m v 24 W (v + 16) 8 ltac:(lia) ltac:(lia))) as C3.
  change [C8 (Z_to_bv 64 x); C8 (Z_to_bv 64 y); C8 (Z_to_bv 64 z)]
    with ([C8 (Z_to_bv 64 x)] ++ [C8 (Z_to_bv 64 y)] ++ [C8 (Z_to_bv 64 z)]).
  apply rw_cells_app. split; [exact C1|]. cbn [cells_size csize].
  replace (v + Z.of_nat (8 + 0)) with (v + 8) by (cbn; lia).
  apply rw_cells_app. split; [exact C2|]. cbn [cells_size csize].
  replace (v + 8 + Z.of_nat (8 + 0)) with (v + 16) by (cbn; lia). exact C3.
Qed.

Lemma wrv_vtrip_opnd : forall LB m v b, vopndA LB m v b 0 25 -> wr_at asegs m v 24 -> rw_cells asegs m v (vtrip b 500).
Proof.
  intros LB m v b V W. unfold vopndA, vec_opnd in V. destruct V as (_ & _ & _ & _ & _ & F1 & F2 & F3).
  unfold OPND_SZ in F2, F3. rewrite Z.mul_0_r, Z.add_0_r in F2. unfold vtrip. exact (wrv_trip m v b b (b + 500) W F1 F2 F3).
Qed.

Lemma wrv_vtrip32 : forall LB m v b, vec32A LB m v b [] 25 -> wr_at asegs m v 24 -> rw_cells asegs m v (vtrip b 100).
Proof.
  intros LB m v b V W. unfold vec32A, vec32 in V. destruct V as (_ & _ & _ & _ & _ & F1 & F2 & F3 & _).
  change (Zlen (@nil Z)) with 0 in F2. rewrite Z.mul_0_r, Z.add_0_r in F2. unfold vtrip. exact (wrv_trip m v b b (b + 100) W F1 F2 F3).
Qed.

Lemma wrv_wblk : forall LBo m (pid : bptr) b n, lb_own ((pid, b, n) :: LBo) m -> SHAD m b (cc_gen n 0) -> wblk m b n.
Proof.
  intros LBo m pid b n OW SH. split; [|exact SH].
  exact (lb_own_In _ _ (pid, b, n) OW (or_introl eq_refl)).
Qed.

Section WoRv.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Lemma wrv_win : forall (e : went H) ff fp XSc sk LBk m LB v,
    wpre H e -> winv H e ff fp XSc sk LBk m -> ff + 8 <= v -> v + 24 <= ff + WO_FLAGP -> v mod 8 = 0 ->
    obj_win H LB ((6, ff, fp) :: w_LF e) (wS1 e) (w_lo e) v 24
    /\ ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47))
    /\ wr_at asegs m v 24.
  Proof.
    intros e ff fp XSc sk LBk m LB v HP HI V1 V2 V8.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & ACL).
    pose proof (wframe_bounds H e ff fp XSc sk LBk m HP HI)
      as (F0 & F64 & FLO & FH & FL & FS & SH1 & SH2 & S1L' & S1SP' & SPH' & LOS1').
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI))
      as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    assert (WW : wwin H e ff (v, v + 24)) by (unfold wwin; right; left; cbn [fst snd]; lia).
    destruct (wwin_ok H e ff fp XSc (v, v + 24) (winv_ff H _ _ _ _ _ _ _ HI) CE
                ltac:(unfold WO_SAVED; lia) ltac:(lia) WW) as (AFS & ACW & ACO & _).
    unfold WO_FLAGP in *.
    split; [|split].
    - unfold obj_win. split; [|split; [|split; [|split; [|split]]]].
      + unfold aclient_range. right; right; right; right; left. lia.
      + unfold aclient_range. right; right; right; right; right; left.
        clear - G5 G6 G7 G8 G9 V1 V2 V8 F0. unfold sh, nsh. Z.div_mod_to_equations. lia.
      + exact (ACW LB).
      + exact AFS.
      + exact ACO.
      + left. lia.
    - unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in G10.
      destruct G10 as [[X Y]|[X Y]]; [left | right]; lia.
    - pose proof (winv_wf H _ _ _ _ _ _ _ HI) as (W0 & W1 & W). unfold WO_FLAGP in *.
      split; [lia|]. split; [lia|]. intros i Hi. replace (v + i) with (ff + (v - ff + i)) by lia. apply W. lia.
  Qed.

  Lemma wrv_opnd : forall (e : went H) ff fp XSc s LB LBo m msF mo (Q : config -> Prop)
      (ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (v : Z)
      (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc s LB m -> (forall b, In b (w_LB e) -> In b LB) ->
    as_VIS H s msF = MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 25)
                           a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 RESV_OPND_ENTRY) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> bv_unsigned ra mod 2 = 0 -> 0 <= as_AL H s ->
    rw_cells asegs m v [CB 24 (poison_bytes 24 0)] -> addressable m v 24 ->
    ff + 8 <= v -> v + 24 <= ff + WO_FLAGP -> v mod 8 = 0 ->
    lb_own LBo m -> (forall b, In b LBo -> In b LB) -> List.NoDup (map blk_id LBo) ->
    lb_small LB + 500 <= RT_SMALL_MAX -> Z.of_nat (length LB) + 1 <= RT_CNT_MAX -> nlarge LB <= RT_LARGE_MAX ->
    trace_ok (as_TR H) APC0_FREE [RESV_OPND_DEL_RA] ->
    (forall msF' mo' s' (pid : bptr) (b' : Z) m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       as_VIS H s' msF' = MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       winv H e ff fp XSc s' ((pid, b', 500) :: LB) m' ->
       xpres H LB (wS1 e) [(v, v + 24)] m m' -> ~ In pid (map blk_id LB) ->
       vopndA ((pid, b', 500) :: LB) m' v b' 0 25 -> ablock_range H b' 500 -> SHAD m' b' (cc_gen 500 0) ->
       addressable m' v 24 -> wr_at asegs m' v 24 -> lb_own ((pid, b', 500) :: LBo) m' ->
       List.NoDup (map blk_id ((pid, b', 500) :: LBo)) ->
       as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e ff fp XSc s LB LBo m msF mo Q ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 v F fc
      HP HI INC VIS KR RA2 AL0 Z24v ADv V1 V2 V8 OWN OINC ND LS LC LL TRO K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & ACL).
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    destruct (winv_er H _ _ _ _ _ _ _ HI) as (errv & ER).
    pose proof (rt_bp_cost H HHb) as (CF0 & CM0).
    assert (CM : as_Cm H 500 = 0) by (rewrite CM0; apply ICM_small; lia).
    assert (SPB : wSP e <= w_B e) by (clear - HP; unfold wpre in HP; cbv zeta in HP; tauto).
    destruct (wrv_win e ff fp XSc s LB m LB v HP HI V1 V2 V8) as (OW & REG & WRv).
    assert (FB := wframe_bounds H e ff fp XSc s LB m HP HI).
    eapply (ah_seq H HB).
    { eapply (resv_opnd_ok H HB ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 25)
                a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LBo ((6, ff, fp) :: w_LF e)
                v 0 0 0 25 0 (w_lo e) (w_B e) (w_shi e) errv);
        rewrite ?HLib.u64_of_Z by lia.
      - exact VIS.
      - reflexivity.
      - reflexivity.
      - unfold vopndA. apply vec_opnd_nil; [lia | lia | | | |].
        + exact (mdef_of_rw_cells_hi m v _ Z24v ltac:(unfold AIMG_TOP; lia)).
        + replace v with (v + 0) at 1 by lia. apply z24_fld; [exact Z24v | lia].
        + apply z24_fld; [exact Z24v | lia].
        + apply z24_fld; [exact Z24v | lia].
      - exact V8.
      - exact ADv.
      - exact OW.
      - exact REG.
      - exact WRv.
      - exact OWN.
      - exact OINC.
      - exact ND.
      - left. split; reflexivity.
      - intros X. lia.
      - lia.
      - unfold OPND_SZ. lia.
      - exact RH.
      - exact KR.
      - intros _. split.
        + apply (rt_bp_live H HHb s LB m (OPND_SZ * 25) RH);
            [unfold OPND_SZ; lia | change (nsmall (OPND_SZ * 25)) with 500; lia | exact LC | change (nlg (OPND_SZ * 25)) with 0; lia].
        + rewrite CF0. change (OPND_SZ * 25) with 500. rewrite CM. lia.
      - exact TRO.
      - exact (winv_ra H _ _ _ _ _ _ _ HI).
      - lia.
      - clear - S32. Z.div_mod_to_equations. lia.
      - lia.
      - exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))).
      - exact CE.
      - unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK. lia.
      - exact ER.
      - exact (winv_mi H _ _ _ _ _ _ _ HI).
      - exact TP.
      - exact RA2.
      - exact (winv_ac H _ _ _ _ _ _ _ HI).
      - exact (winv_rf H _ _ _ _ _ _ _ HI).
      - exact (winv_s0 H _ _ _ _ _ _ _ HI).
      - lia. }
    intros [msF' mo'] POST.
    destruct POST as (u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m' & errv' & s' & pid' & b' & cap'
                      & POST).
    cbv zeta in POST.
    destruct POST as (VIS' & KR' & MP' & MI' & ST' & ER' & RA' & XP & _ & CK & RH' & VEC' & AD' & WR' & OWN' & RF' & AC' & S0').
    cbn [cfg_ms cfg_model] in VIS', KR', MP'.
    rewrite HLib.u64_of_Z in ST', XP by lia.
    destruct (CK ltac:(lia)) as (Ecap & ABR & SHB & AL'). subst cap'.
    change (if 25 <=? 0 then LB else v4_newLB H LB 0 0 pid' b' (OPND_SZ * 25)) with ((pid', b', 500) :: LB) in RH', VEC'.
    change (if 25 <=? 0 then LBo else v4_newLB H LBo 0 0 pid' b' (OPND_SZ * 25)) with ((pid', b', 500) :: LBo) in OWN'.
    change (OPND_SZ * 25) with 500 in ABR, SHB. change (OPND_SZ * 0) with 0 in SHB.
    assert (XP' : xpres H LB (wS1 e) [(v, v + 24)] m m') by exact XP.
    assert (NI : ~ In pid' (map blk_id LB)).
    { pose proof (ah_nodup H HB _ _ _ RH') as NDh. cbn [map] in NDh. apply NoDup_cons_iff in NDh as [NDh _]. exact NDh. }
    eapply (K msF' mo' s' pid' b' m' u0 u1 u2 c0 c1 c2 c3 c4 c5 c6 c7 u3 u4 u5 u6);
      [exact VIS' | exact KR' | exact MP' | | exact XP' | exact NI | exact VEC' | exact ABR | exact SHB | exact AD' | exact WR'
      | exact OWN' | cbn [map]; apply List.NoDup_cons; [intros Hin; apply NI; apply in_map_iff in Hin as (bb & Eb & Hb); apply in_map_iff; exists bb; split; [exact Eb | exact (OINC bb Hb)] | exact ND] | rewrite CF0 in AL'; change (OPND_SZ * 25) with 500 in AL'; rewrite CM in AL'; lia].
    rewrite <- (app_nil_r XSc).
    pose proof FB as (F0 & F64 & FLO & FH & FL & FS & SH1 & SH2 & _).
    eapply (winv_sr H HB e ff fp XSc [] [(v, v + 24)] s LB LB s' ((pid', b', 500) :: LB) m m' HP HI INC XP' (Forall_nil _)).
    - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. right; left. unfold WO_FLAGP in *. lia.
    - exact RF'.
    - exact RH'.
    - exact AC'.
    - exact MI'.
    - exact ST'.
    - exists errv'. exact ER'.
    - exact RA'.
    - apply Forall_cons; [|apply Forall_nil]. intros _. cbn [fst snd]. replace (v + 24 - v) with 24 by lia. exact WR'.
  Qed.

  Lemma wrv32 : forall (c : rv_consts), resv32_stmt H c -> forall (e : went H) ff fp XSc s LB LBo m msF mo (Q : config -> Prop)
      (ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (v : Z)
      (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc s LB m -> (forall b, In b (w_LB e) -> In b LB) ->
    as_VIS H s msF = MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 25)
                           a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 (rv_entry c)) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> bv_unsigned ra mod 2 = 0 -> 0 <= as_AL H s ->
    rw_cells asegs m v [CB 24 (poison_bytes 24 0)] -> addressable m v 24 ->
    ff + 8 <= v -> v + 24 <= ff + WO_FLAGP -> v mod 8 = 0 ->
    lb_own LBo m -> (forall b, In b LBo -> In b LB) -> List.NoDup (map blk_id LBo) ->
    lb_small LB + 100 <= RT_SMALL_MAX -> Z.of_nat (length LB) + 1 <= RT_CNT_MAX -> nlarge LB <= RT_LARGE_MAX ->
    trace_ok (as_TR H) APC0_FREE [rv_del_ra c] ->
    (forall msF' mo' s' (pid : bptr) (b' : Z) m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       as_VIS H s' msF' = MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       winv H e ff fp XSc s' ((pid, b', 100) :: LB) m' ->
       xpres H LB (wS1 e) [(v, v + 24)] m m' -> ~ In pid (map blk_id LB) ->
       vec32A ((pid, b', 100) :: LB) m' v b' [] 25 -> ablock_range H b' 100 -> SHAD m' b' (cc_gen 100 0) ->
       addressable m' v 24 -> wr_at asegs m' v 24 -> lb_own ((pid, b', 100) :: LBo) m' ->
       List.NoDup (map blk_id ((pid, b', 100) :: LBo)) ->
       as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros c RSV e ff fp XSc s LB LBo m msF mo Q ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 v F fc
      HP HI INC VIS KR RA2 AL0 Z24v ADv V1 V2 V8 OWN OINC ND LS LC LL TRO K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & ACL).
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    destruct (winv_er H _ _ _ _ _ _ _ HI) as (errv & ER).
    pose proof (rt_bp_cost H HHb) as (CF0 & CM0).
    assert (CM : as_Cm H 100 = 0) by (rewrite CM0; apply ICM_small; lia).
    assert (SPB : wSP e <= w_B e) by (clear - HP; unfold wpre in HP; cbv zeta in HP; tauto).
    destruct (wrv_win e ff fp XSc s LB m LB v HP HI V1 V2 V8) as (OW & REG & WRv).
    assert (FB := wframe_bounds H e ff fp XSc s LB m HP HI).
    eapply (ah_seq H HB).
    { eapply (RSV ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 25)
                a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LBo ((6, ff, fp) :: w_LF e)
                v 0 [] 0 25 0 (w_lo e) (w_B e) (w_shi e) errv);
        rewrite ?HLib.u64_of_Z by lia.
      - exact VIS.
      - reflexivity.
      - reflexivity.
      - unfold vec32A. apply vec32_nil; [lia | lia | | | |].
        + exact (mdef_of_rw_cells_hi m v _ Z24v ltac:(unfold AIMG_TOP; lia)).
        + replace v with (v + 0) at 1 by lia. apply z24_fld; [exact Z24v | lia].
        + apply z24_fld; [exact Z24v | lia].
        + apply z24_fld; [exact Z24v | lia].
      - exact V8.
      - exact ADv.
      - exact OW.
      - exact REG.
      - exact WRv.
      - exact OWN.
      - exact OINC.
      - exact ND.
      - left. split; reflexivity.
      - intros X. lia.
      - lia.
      - lia.
      - exact RH.
      - exact KR.
      - intros _. split.
        + apply (rt_bp_live H HHb s LB m (4 * 25) RH);
            [lia | change (nsmall (4 * 25)) with 100; lia | exact LC | change (nlg (4 * 25)) with 0; lia].
        + rewrite CF0. change (4 * 25) with 100. rewrite CM. lia.
      - exact TRO.
      - exact (winv_ra H _ _ _ _ _ _ _ HI).
      - lia.
      - clear - S32. Z.div_mod_to_equations. lia.
      - lia.
      - exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))).
      - exact CE.
      - unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK. lia.
      - exact ER.
      - exact (winv_mi H _ _ _ _ _ _ _ HI).
      - exact TP.
      - exact RA2.
      - exact (winv_ac H _ _ _ _ _ _ _ HI).
      - exact (winv_rf H _ _ _ _ _ _ _ HI).
      - exact (winv_s0 H _ _ _ _ _ _ _ HI).
      - lia. }
    intros [msF' mo'] POST.
    destruct POST as (u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m' & errv' & s' & pid' & b' & cap'
                      & POST).
    cbv zeta in POST.
    destruct POST as (VIS' & KR' & MP' & MI' & ST' & ER' & RA' & XP & _ & CK & RH' & VEC' & AD' & WR' & OWN' & RF' & AC' & S0').
    cbn [cfg_ms cfg_model] in VIS', KR', MP'.
    rewrite HLib.u64_of_Z in ST', XP by lia.
    destruct (CK ltac:(lia)) as (Ecap & ABR & SHB & AL'). subst cap'.
    change (if 25 <=? 0 then LB else v4_newLB H LB 0 0 pid' b' (4 * 25)) with ((pid', b', 100) :: LB) in RH', VEC'.
    change (if 25 <=? 0 then LBo else v4_newLB H LBo 0 0 pid' b' (4 * 25)) with ((pid', b', 100) :: LBo) in OWN'.
    change (4 * 25) with 100 in ABR, SHB. change (4 * Zlen (@nil Z)) with 0 in SHB.
    assert (XP' : xpres H LB (wS1 e) [(v, v + 24)] m m') by exact XP.
    assert (NI : ~ In pid' (map blk_id LB)).
    { pose proof (ah_nodup H HB _ _ _ RH') as NDh. cbn [map] in NDh. apply NoDup_cons_iff in NDh as [NDh _]. exact NDh. }
    eapply (K msF' mo' s' pid' b' m' u0 u1 u2 c0 c1 c2 c3 c4 c5 c6 c7 u3 u4 u5 u6);
      [exact VIS' | exact KR' | exact MP' | | exact XP' | exact NI | exact VEC' | exact ABR | exact SHB | exact AD' | exact WR'
      | exact OWN' | cbn [map]; apply List.NoDup_cons; [intros Hin; apply NI; apply in_map_iff in Hin as (bb & Eb & Hb); apply in_map_iff; exists bb; split; [exact Eb | exact (OINC bb Hb)] | exact ND] | rewrite CF0 in AL'; change (4 * 25) with 100 in AL'; rewrite CM in AL'; lia].
    rewrite <- (app_nil_r XSc).
    pose proof FB as (F0 & F64 & FLO & FH & FL & FS & SH1 & SH2 & _).
    eapply (winv_sr H HB e ff fp XSc [] [(v, v + 24)] s LB LB s' ((pid', b', 100) :: LB) m m' HP HI INC XP' (Forall_nil _)).
    - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. right; left. unfold WO_FLAGP in *. lia.
    - exact RF'.
    - exact RH'.
    - exact AC'.
    - exact MI'.
    - exact ST'.
    - exists errv'. exact ER'.
    - exact RA'.
    - apply Forall_cons; [|apply Forall_nil]. intros _. cbn [fst snd]. replace (v + 24 - v) with 24 by lia. exact WR'.
  Qed.

  Lemma wrv_fsb : forall (e : went H) ff fp XSc sk LBk m, wpre H e -> winv H e ff fp XSc sk LBk m ->
    as_FSB H <= ff /\ ff + 4096 <= as_FSB H + AFS_SIZE /\ ff mod 64 = 0 /\ ff + 4096 <= aceil
    /\ ((0x6e8000 <= ff /\ ff + 4096 <= 0x7fff7000) \/ (0x10007fff8000 <= ff /\ ff + 4096 <= aceil)).
  Proof.
    intros e ff fp XSc sk LBk m HP HI.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI))
      as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in G10.
    split; [lia|]. split; [lia|]. split; [exact G3|]. split; [lia|].
    destruct G10 as [[X Y]|[X Y]]; [left | right]; lia.
  Qed.

  Lemma wrv_xcells : forall (e : went H) ff fp XSc sk LBk LB m m' X A cs,
    wpre H e -> winv H e ff fp XSc sk LBk m -> xpres H LB (wS1 e) X m m' -> rw_cells asegs m A cs ->
    ff <= A -> A + Z.of_nat (cells_size cs) <= ff + 4096 ->
    Forall (fun iv : Z * Z => A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) X -> rw_cells asegs m' A cs.
  Proof.
    intros e ff fp XSc sk LBk LB m m' X A cs HP HI XP C A1 A2 FX.
    destruct (wrv_fsb e ff fp XSc sk LBk m HP HI) as (B1 & B2 & _).
    eapply (xpres_rw_cells H); [exact XP | exact C |]. split; [| exact FX].
    unfold aclient_range. right; right; right; right; left. lia.
  Qed.

  Lemma wrv_xaddr : forall (e : went H) ff fp XSc sk LBk LB m m' X A n,
    wpre H e -> winv H e ff fp XSc sk LBk m -> xpres H LB (wS1 e) X m m' -> addressable m A n ->
    ff <= A -> A + n <= ff + WO_FLAGP ->
    Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) X -> addressable m' A n.
  Proof.
    intros e ff fp XSc sk LBk LB m m' X A n HP HI XP AD A1 A2 FX.
    destruct (wrv_fsb e ff fp XSc sk LBk m HP HI) as (B1 & B2 & F64 & FC & FAPP).
    pose proof aceil_facts as ACF.
    destruct AD as (N0 & A0 & A8 & U). split; [exact N0|]. split; [exact A0|]. split; [exact A8|].
    eapply (xpres_u8arr H); [exact XP | exact U |].
    rewrite (shadow_of_length n N0). unfold WO_FLAGP in A2.
    split.
    - unfold aclient_range. right; right; right; right; right; left.
      clear - B1 B2 A1 A2 A8 N0. unfold sh, nsh. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact FX]. intros iv K. cbn in K.
      clear - K FAPP ACF A1 A2 A8 N0 FC. unfold sh, nsh in *. rewrite ASHADOW_BASE_val in *.
      destruct FAPP as [[X Y]|[X Y]]; [right | left]; Z.div_mod_to_equations; lia.
  Qed.

  Lemma wrv_blk_apart : forall s LB m q b n (e : went H) ff fp XSc sk LBk m0 X,
    as_RHEAP H s LB m -> In (q, b, n) LB -> wpre H e -> winv H e ff fp XSc sk LBk m0 ->
    Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) X ->
    Forall (fun iv : Z * Z => b + n <= fst iv \/ snd iv <= b) X
    /\ Forall (fun iv : Z * Z => sh b + nsh n <= fst iv \/ snd iv <= sh b) X
    /\ 0 < b /\ b mod 16 = 0 /\ 0 <= n /\ b + n <= aceil.
  Proof.
    intros s LB m q b n e ff fp XSc sk LBk m0 X RH IN HP HI FX.
    pose proof (ah_blocks H HB _ _ _ _ RH IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
    destruct (wrv_fsb e ff fp XSc sk LBk m0 HP HI) as (F1 & F2 & F64 & FC & FAPP).
    pose proof aceil_facts as ACF.
    split; [|split; [| repeat split; lia]].
    - eapply Forall_impl; [| exact FX]. intros iv K. cbn in K. lia.
    - eapply Forall_impl; [| exact FX]. intros iv K. cbn in K.
      clear - K FAPP ACF BC B0 Bn B16 FC. unfold sh, nsh in *. rewrite ASHADOW_BASE_val in *.
      destruct FAPP as [[X Y]|[X Y]]; [right | left]; Z.div_mod_to_equations; lia.
  Qed.

  Lemma wrv_noriv : forall X A n, Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X ->
    forall a, A <= a < A + n -> ~ rin_ivs X a.
  Proof.
    intros X A n FX a Ha. apply rin_ivs_none. eapply Forall_impl; [| exact FX]. intros iv K. cbn in K. lia.
  Qed.

  Lemma wrv_xblk : forall (e : went H) ff fp XSc sk LBk s LB m m' X (q : bptr) b n,
    wpre H e -> winv H e ff fp XSc sk LBk m -> as_RHEAP H s LB m -> xpres H LB (wS1 e) X m m' ->
    Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) X ->
    In (q, b, n) LB -> wblk m b n -> wblk m' b n.
  Proof.
    intros e ff fp XSc sk LBk s LB m m' X q b n HP HI RH XP FX IN (W & S0 & S8 & U).
    destruct (wrv_blk_apart s LB m q b n e ff fp XSc sk LBk m X RH IN HP HI FX) as (D1 & D2 & B0 & B16 & Bn & BC).
    split; [| split; [exact S0 | split; [exact S8|]]].
    - eapply (xpres_wr_at H); [exact XP | exact W |]. split; [| exact D1].
      unfold aclient_range. right; right; left. exists (q, b, n). cbn. split; [exact IN | lia].
    - eapply (xpres_u8arr H); [exact XP | exact U |]. rewrite cc_gen_length by lia. split; [| exact D2].
      unfold aclient_range. right; right; right; left. exists (q, b, n). cbn. split; [exact IN | lia].
  Qed.

  Lemma wrv_xstate : forall (e : went H) ff fp XSc sk LBk s LB LB' m m' X st c,
    wpre H e -> winv H e ff fp XSc sk LBk m -> as_RHEAP H s LB m -> xpres H LB (wS1 e) X m m' ->
    Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) X ->
    Forall (fun iv : Z * Z => st + 240 <= fst iv \/ snd iv <= st) X -> ff <= st -> st + 240 <= ff + 4096 ->
    (forall p n, In (p, n) (state_blocks c) -> In (p, n) (lbl LB) /\ In (p, n) (lbl LB')) ->
    state_repA LB m st c -> state_sh m c -> state_repA LB' m' st c /\ state_sh m' c.
  Proof.
    intros e ff fp XSc sk LBk s LB LB' m m' X st c HP HI RH XP FX FS S1 S2 BL R S.
    destruct (wrv_fsb e ff fp XSc sk LBk m HP HI) as (F1 & F2 & F64 & FC & FAPP).
    assert (BA : forall p n, In (p, n) (state_blocks c) ->
                   Forall (fun iv : Z * Z => p + n <= fst iv \/ snd iv <= p) X
                   /\ Forall (fun iv : Z * Z => sh p + nsh n <= fst iv \/ snd iv <= sh p) X).
    { intros p n Hin. destruct (BL p n Hin) as [L1 _]. destruct (lbl_in_inv _ _ _ L1) as (q & Hq).
      destruct (wrv_blk_apart s LB m q p n e ff fp XSc sk LBk m X RH Hq HP HI FX) as (D1 & D2 & _). split; assumption. }
    split.
    - eapply (rep_keep H LB LB' LB (wS1 e) X m m' st c R XP).
      + apply (objx_intro H). { left. lia. }
        intros a Ha _. exact (wrv_noriv X st 240 FS a Ha).
      + apply (blkx_intro H). intros p n Hin. destruct (BL p n Hin) as [L1 L2]. split; [exact L1|]. split; [exact L2|].
        exact (wrv_noriv X p n (proj1 (BA p n Hin))).
      + destruct FAPP as [[X1 Y]|[X1 Y]]; unfold AIMG_TOP; lia.
      + pose proof aceil_facts. lia.
    - eapply (sh_keep H LB LB (wS1 e) X m m' st c R S XP).
      apply (blksh_intro H). intros p n Hin. destruct (BL p n Hin) as [L1 _]. split; [exact L1|].
      exact (wrv_noriv X (sh p) (nsh n) (proj2 (BA p n Hin))).
  Qed.

  Lemma wrv_xs1 : forall (e : went H) ff fp XSc sk LBk LB m m' X A cs,
    wpre H e -> winv H e ff fp XSc sk LBk m -> xpres H LB (wS1 e) X m m' -> rw_cells asegs m A cs -> wS1 e <= A ->
    Forall (fun iv : Z * Z => A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) X -> rw_cells asegs m' A cs.
  Proof.
    intros e ff fp XSc sk LBk LB m m' X A cs HP HI XP C A1 FX.
    eapply (xpres_rw_cells H); [exact XP | exact C |]. split; [| exact FX]. unfold aclient_range. left. exact A1.
  Qed.

  Lemma wrv_xshwr : forall (e : went H) ff fp XSc sk LBk LB m m' X o k,
    wpre H e -> winv H e ff fp XSc sk LBk m -> xpres H LB (wS1 e) X m m' -> wr_at asegs m (sh ff + o) k ->
    0 <= o -> 0 <= k -> o + k <= 512 ->
    Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) X -> wr_at asegs m' (sh ff + o) k.
  Proof.
    intros e ff fp XSc sk LBk LB m m' X o k HP HI XP W O0 K0 OK FX.
    destruct (wrv_fsb e ff fp XSc sk LBk m HP HI) as (B1 & B2 & F64 & FC & FAPP).
    pose proof aceil_facts as ACF.
    eapply (xpres_wr_at H); [exact XP | exact W |]. split.
    - unfold aclient_range. right; right; right; right; right; left.
      clear - B1 B2 F64 O0 K0 OK. unfold sh. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact FX]. intros iv Kv. cbn in Kv.
      clear - Kv FAPP ACF F64 O0 K0 OK FC. unfold sh in *. rewrite ASHADOW_BASE_val in *.
      destruct FAPP as [[X Y]|[X Y]]; [right | left]; Z.div_mod_to_equations; lia.
  Qed.

  Definition wrv_w32 := wrv32 RESV_W32 (resv_w32_ok H HB).
  Definition wrv_typ := wrv32 RESV_TYP (resv_typ_ok H HB).

End WoRv.

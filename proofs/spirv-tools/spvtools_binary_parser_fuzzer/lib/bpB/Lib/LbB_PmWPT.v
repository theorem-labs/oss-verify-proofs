(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_DStat LbB_PmBase LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmVops LbB_PmDS LbB_WoGen LbB_ContStmt LbB_TablStmt LbB_PmWKit LbB_PmWG.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WPT.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.

  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.

  Let HH : asan_rt_hyps H := proj1 HHbp.

  Lemma pmw_meas_LB3 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    lb_small LB + 3 * 64512 <= RT_SMALL_MAX /\ Z.of_nat (length LB) + 2 <= RT_CNT_MAX /\ nlarge LB + 2 <= RT_LARGE_MAX.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal OK X.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    pose proof (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (M1 & M2 & M3).
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [_ TBL].
    pose proof (wk_meas0 H w OK) as (W1 & W2 & W3).
    pose proof (tb_meas TB TBL) as (T1 & T2 & T3).
    rewrite (lb_small_perm _ _ OWN1), (nlarge_perm _ _ OWN1), (Permutation_length OWN1).
    rewrite !lb_small_app, !nlarge_app, !length_app.
    pose proof (nlarge_nonneg (wa_LB0 w)). pose proof (nlarge_nonneg LBs).
    unfold RT_SMALL_MAX, RT_CNT_MAX, RT_LARGE_MAX, po_small, po_cnt, po_large in *. lia.
  Qed.

  Lemma pm_pat_call : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F (pc : Z) fc (ret STK capm : Z)
      (ys : list Z) (R0 : word -> Prop) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 4%bv = wa_tp w ->
    0 <= STK <= APM_STACK - 1248 ->
    t3c (c_v3 c) <= capm ->
    (forall b'' xs'' cap'', 0 <= cap'' <= capm -> pm_bud (wa_n w) (set_v3A c (b'', xs'', cap''))) ->
    trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] -> trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF] ->

    (forall (pid : bptr) (errv : word),
       (t3a (c_v3 c) <> 0 -> In (pid, t3a (c_v3 c), 4 * t3c (c_v3 c)) LBs) ->
       pat_pre H (PropExec.getr R 1%bv) (PropExec.getr R 2%bv) (PropExec.getr R 4%bv) msF m mo s LB (PMLF H w)
               (wa_p w + O_V3) (t3a (c_v3 c)) (t3c (c_v3 c)) capm (t3b (c_v3 c)) pid (wa_lo w) (wa_B w) (wa_shi w) STK errv ->
       as_SR H (pat_post H (PropExec.getr R 1%bv) (PropExec.getr R 2%bv) (PropExec.getr R 3%bv) (PropExec.getr R 4%bv)
                  (PropExec.getr R 8%bv) (PropExec.getr R 9%bv) (PropExec.getr R 18%bv) (PropExec.getr R 19%bv) (PropExec.getr R 20%bv)
                  (PropExec.getr R 21%bv) (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) (PropExec.getr R 24%bv) (PropExec.getr R 25%bv)
                  (PropExec.getr R 26%bv) (PropExec.getr R 27%bv) F fc s LB (PMLF H w) (wa_p w + O_V3) (t3a (c_v3 c)) (t3c (c_v3 c))
                  capm ys pid (wa_lo w) (wa_B w) (wa_shi w) m mo R0)
         (mkCfg msF mo)) ->
    (forall msF1 mo1 m1 R1 (s1 : as_St H) (LB1 LBs1 : list block) (b' cap' : Z),
       as_AKREL H s1 (mkCfg msF1 mo1) ->
       as_VIS H s1 msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s1 LB1 LBs1 m1 mo1 (set_v3A c (b', ys, cap')) ins tbl ftbl TB spal ->
       (forall r, In r V4_KEPT -> PropExec.getr R1 r = PropExec.getr R r) ->
       R0 (PropExec.getr R1 10%bv) ->
       pm_bud (wa_n w) (set_v3A c (b', ys, cap')) -> t3c (c_v3 c) <= cap' <= capm ->
       ((b' = t3a (c_v3 c) /\ cap' = t3c (c_v3 c) /\ LB1 = LB /\ LBs1 = LBs) \/ (t3c (c_v3 c) < cap' /\ ablock_range H b' (4 * cap'))) ->
       (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
          rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F pc fc ret STK capm ys R0 Q OK X Hknn Hfk KR VIS RF
           G1 Hr2 Hr G2 G4 HSTK HCM BUDm TRC TRR CALL K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16). pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (wk_s1 H w OK) as [T1 T2].
    pose proof (wk_n H w OK) as WN. pose proof (wk_lfb H w OK) as LFB.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as V3.
    pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (SHc & ADp & _).
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (A1 & A2 & A3 & A4).
    destruct (c_v3 c) as [[b xs] cap] eqn:EV3. cbn [t3a t3b t3c fst snd] in *.
    pose proof V3 as (Hv & Hv' & HD & Hlen & Hb & _).
    assert (Hcap0 : 0 <= cap) by (unfold Zlen in *; lia).
    assert (B0C : b = 0 -> cap = 0) by (intros B0; destruct Hb as [[_ C0]|(Bp & _)]; lia).

    assert (OLD : exists pid, v4_oldblk LB b cap pid /\ (b <> 0 -> In (pid, b, 4 * cap) LBs)).
    { destruct (Z.eq_dec b 0) as [E|E].
      - exists 0. split; [left; split; [exact E | exact (B0C E)] | intros NZ; contradiction].
      - destruct (cblk_facts H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal b (4 * cap) OK X) as (pid & I1 & I2 & _).
        { rewrite (cblocks_v3 c), EV3. cbn [t3a t3c fst snd]. rewrite !in_app_iff. right; left.
          destruct (Z.eqb_spec b 0); [contradiction | left; reflexivity]. }
        exists pid. split; [right; split; [destruct Hb as [[B0 _]|(Bp & _ & Cp & _)]; [contradiction | exact Cp] | exact I2] | intros _; exact I1]. }
    destruct OLD as (pid & OB & PIDin).
    assert (INbLB : b <> 0 -> In (pid, b, 4 * cap) LB).
    { intros E. apply (Permutation_in _ (Permutation_sym OWN1)). apply in_or_app; right. apply in_or_app; left. exact (PIDin E). }

    set (c'' := set_v3A c (1, [], capm)).
    assert (BUDx : pm_bud (wa_n w) c'') by (unfold c''; apply BUDm; lia).
    pose proof (pm_resv_of_bud (wa_n w) c'' WN BUDx) as RESVx.
    pose proof (phi_set_v3_eq c 1 [] capm ltac:(rewrite EV3; cbn [t3a t3c fst snd]; exact B0C) ltac:(lia)) as PHx.
    fold c'' in PHx. rewrite EV3 in PHx. cbn [t3c snd] in PHx.
    assert (CAPB : 4 * capm <= 2 ^ 26).
    { pose proof BUDx as (_ & _ & _ & _ & _ & _ & Bv3 & _). unfold c'', set_v3A in Bv3. cbn [c_v3 t3c snd] in Bv3. lia. }
    pose proof (pm_phi_le_cap c'') as PCx. pose proof (pm_phi_le_cap c) as PCc.
    assert (ALok : closs cap capm <= as_AL H s) by lia.
    pose proof (pmw_meas_LB3 w s LB LBs m mo c ins tbl ftbl TB spal OK X) as (M1 & M2 & M3).
    destruct (rt_bp_cost H HHbp) as [CFz CMz].
    eapply (ah_seq H HH).
    { apply (CALL pid errv PIDin). unfold pat_pre.
      rewrite G1, G2, G4, !u64_of_Z by lia.
      split; [unfold vec32A; exact V3|]. split; [unfold O_V3; Z.div_mod_to_equations; lia|].
      split; [apply (pw_addr_sub8 m (wa_p w) PARSER_SIZE O_V3 24 ADp); unfold O_V3, PARSER_SIZE; try reflexivity; lia|].
      split; [apply (pwin_obj H HH w LB O_V3 OK); unfold O_V3, PARSER_SIZE; try reflexivity; lia|].
      split; [exact (proj1 (pwin_band H w (wa_p w + O_V3) 24 OK ltac:(unfold O_V3; lia) ltac:(unfold O_V3, PARSER_SIZE; lia) ltac:(lia)))|].
      split; [apply (wr_at_of_mdef m (wa_p w) PARSER_SIZE O_V3 24 (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)); unfold O_V3, PARSER_SIZE; lia|].
      split; [exact (HOWN s LB m RH)|].
      split; [exact OB|].
      split; [intros Cp; pose proof SHc as (_ & _ & _ & _ & _ & SH6); rewrite EV3 in SH6; unfold vsh32 in SH6; cbn [t3a t3b t3c fst snd] in SH6; apply SH6; lia|].
      split; [split; [exact CAPB | exact ALok]|].
      split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
      split; [exact RH|]. split; [exact KR|]. split; [lia|].
      split; [exact TRC|]. split; [exact TRR|].
      split; [exact (xa_rauxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|]. split; [lia|].
      split; [Z.div_mod_to_equations; lia|]. split; [lia|].
      split; [exact (proj1 (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia)))|].
      split; [lia|]. split; [unfold APM_STACK in *; lia|].
      split; [exact ERR|]. split; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|]. split; [exact (wk_tp H w OK)|].
      split; [exact Hr2|].
      split; [exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|]. split; [exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|].
      split; [unfold PMLF; cbn [length]; unfold PM_FRAMES in LFB; lia|].
      split; [exact (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia]. }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB' & b' & cap' & XS & POST).
    cbv zeta in POST.
    destruct POST as (VIS1 & HR0 & KR1 & MP1 & MI1 & ST1 & ER1 & RA1 & VEC1 & RH1 & SH1 & AD1 & WV1 & OW1 & FXS & GROWN & RF1 & AC1' & S01 & AL1).
    cbn [cfg_ms cfg_model] in VIS1, KR1, MP1.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in ST1 by lia. rewrite G4 in ER1. rewrite G2, u64_of_Z in GROWN by lia.
    assert (KEPT1 : forall r, In r V4_KEPT ->
              PropExec.getr (mkR (Z_to_bv 64 ret) (PropExec.getr R 2%bv) (PropExec.getr R 3%bv) (PropExec.getr R 4%bv) t0' t1' t2'
                                  (PropExec.getr R 8%bv) (PropExec.getr R 9%bv) a0' a1' a2' a3' a4' a5' a6' a7'
                                  (PropExec.getr R 18%bv) (PropExec.getr R 19%bv) (PropExec.getr R 20%bv) (PropExec.getr R 21%bv)
                                  (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) (PropExec.getr R 24%bv) (PropExec.getr R 25%bv)
                                  (PropExec.getr R 26%bv) (PropExec.getr R 27%bv) t3' t4' t5' t6') r = PropExec.getr R r).
    { intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0. }
    destruct GROWN as [(ECAP & EB & ELB & XP1) | (GC & (pid' & ELB & ABR1) & XP1)].
    -
      subst cap' b' LB'.
      assert (NZ' : Zlen ys <= cap) by (pose proof VEC1 as (_ & _ & _ & HL' & _); lia).
      assert (BUD1 : pm_bud (wa_n w) (set_v3A c (b, ys, cap))) by (apply BUDm; lia).
      assert (XE : vx H w O_V3 b (4 * cap) ++ XS = (wa_p w + O_V3, wa_p w + O_V3 + 24) :: (b, b + 4 * cap) :: (sh b, sh b + nsh (4 * cap)) :: XS
                   \/ (b = 0 /\ cap = 0)).
      { unfold vx, v4_oldx. destruct (Z.eqb_spec b 0) as [E|E]; [right; split; [exact E | exact (B0C E)] | left; reflexivity]. }
      assert (XP1' : xpres H LB (wa_s1 w) (vx H w O_V3 b (4 * cap) ++ XS) m m1).
      { destruct XE as [-> | [E C0]]; [exact XP1|].
        unfold vx, v4_oldx. rewrite E, Z.eqb_refl. cbn [app].
        eapply (xpres_weaken H); [exact XP1 | lia | intros bb Hbb; exact Hbb |].
        intros a Ha. change (rin_ivs ([(wa_p w + O_V3, wa_p w + O_V3 + 24)] ++ XS) a). apply rin_ivs_app.
        change (rin_ivs ([(wa_p w + O_V3, wa_p w + O_V3 + 24); (b, b + 4 * cap); (sh b, sh b + nsh (4 * cap))] ++ XS) a) in Ha.
        apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [| right; exact Ha]. left.
        cbn [rin_ivs fst snd] in Ha |- *. rewrite E, C0 in Ha. change (nsh (4 * 0)) with 0 in Ha.
        destruct Ha as [Ha|[Ha|[Ha|[]]]]; [left; exact Ha | exfalso; lia | exfalso; lia]. }
      assert (X1 : PMXAT H LINV w s1 LB LBs m1 mo1 (set_v3A c (b, ys, cap)) ins tbl ftbl TB spal).
      { destruct (pmxa_keep_but_xp H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal m1 (lbl LB) (vx H w O_V3 b (4 * cap)) XS O_V3 (b, 4 * cap)
                    OK X RF1 FXS XP1' (vx_vwin H w O_V3 b (4 * cap) ltac:(lia)) ltac:(unfold O_V1, O_V3; lia) ltac:(unfold O_V3, PARSER_SIZE; lia)
                    ltac:(right; right; split; [reflexivity | unfold blkV3; rewrite EV3; reflexivity]) ltac:(intros q _ _ Hl; exact Hl))
          as (U1 & U2 & U3 & Z1 & Z2 & Z3 & K1 & K2 & _).
        destruct (K1 ltac:(unfold O_V1, O_V3; lia)) as [V1 Z4]. destruct (K2 ltac:(unfold O_V2, O_V3; lia)) as [V2 Z5].
        eapply (pmxa_vsame_gen H HHbp LINV LINV_cl HOWN w s LB LBs m mo c ins tbl ftbl TB spal s1 m1 mo1 (set_v3A c (b, ys, cap)) O_V3 pid b (4 * cap) XS
                  OK X Hknn Hfk ltac:(unfold O_V1, O_V3; lia) ltac:(unfold O_V3, PARSER_SIZE; lia));
          [ rewrite cblocks_set_v3, (cblocks_v3 c), EV3; cbn [t3a t3c fst snd]; reflexivity
          | exact PIDin | lia
          | reflexivity | reflexivity | reflexivity | reflexivity
          | exact RH1 | exact MP1 | exact MI1 | exact ST1 | exists errv1; exact ER1 | exact RA1 | exact FXS | exact XP1' | exact WV1 | exact RF1 | exact AC1' | exact S01
          | rewrite closs_refl in AL1; lia
          | exact U1 | exact U2 | exact U3 | exact V1 | exact V2 | exact VEC1 | ].
        unfold set_v3A, pmc_sh. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3]. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|].
        split; [exact Z4|]. split; [exact Z5|].
        unfold vsh32. cbn [t3a t3b t3c fst snd]. intros NZ. apply SH1. destruct Hb as [[B0 _]|(Bp & _ & Cp & _)]; [contradiction | exact Cp]. }
      eapply (K ms1 mo1 m1 _ s1 LB LBs b cap); [exact KR1 | exact VIS1 | apply rfull_mkR | exact X1 | exact KEPT1 | exact HR0 | exact BUD1 | lia
                | left; repeat split; reflexivity |].
      intros k cs Hk Hkc RWk.
      exact (vx_ff_keep H HHbp w s LB m m1 O_V3 b (4 * cap) pid XS k cs OK RH RF1 FXS ltac:(unfold O_V1, O_V3; lia) ltac:(unfold O_V3, PARSER_SIZE; lia) INbLB ltac:(lia) XP1' Hk Hkc RWk).
    -
      subst LB'.
      assert (NZ' : Zlen ys <= cap') by (pose proof VEC1 as (_ & _ & _ & HL' & _); lia).
      assert (BUD1 : pm_bud (wa_n w) (set_v3A c (b', ys, cap'))) by (apply BUDm; lia).
      pose proof ABR1 as (B'0 & _).
      pose proof (phi_set_v3_eq c b' ys cap' ltac:(rewrite EV3; cbn [t3a t3c fst snd]; exact B0C) ltac:(lia)) as PG. rewrite EV3 in PG. cbn [t3c snd] in PG.
      assert (X1 : PMXAT H LINV w s1 (v4_newLB H LB b pid pid' b' (4 * cap')) ((pid', b', 4 * cap') :: (if b =? 0 then LBs else as_lb_remove H pid LBs)) m1 mo1
                     (set_v3A c (b', ys, cap')) ins tbl ftbl TB spal).
      { destruct (pmxa_keep_but_xp H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal m1 (lbl (v4_newLB H LB b pid pid' b' (4 * cap'))) (vx H w O_V3 b (4 * cap)) XS O_V3 (b, 4 * cap)
                    OK X RF1 FXS XP1 (vx_vwin H w O_V3 b (4 * cap) ltac:(lia)) ltac:(unfold O_V1, O_V3; lia) ltac:(unfold O_V3, PARSER_SIZE; lia)
                    ltac:(right; right; split; [reflexivity | unfold blkV3; rewrite EV3; reflexivity]))
          as (U1 & U2 & U3 & Z1 & Z2 & Z3 & K1 & K2 & _).
        { intros q Hq Hne Hl. eapply (vgrow_live H HHbp w s LB LBs TB m c pid pid' b (4 * cap) b' (4 * cap') (b, 4 * cap) q OK RH OWN1 OWN2 eq_refl PIDin Hq Hne Hl). }
        destruct (K1 ltac:(unfold O_V1, O_V3; lia)) as [V1 Z4]. destruct (K2 ltac:(unfold O_V2, O_V3; lia)) as [V2 Z5].
        eapply (pmxa_vgrow_gen H HHbp LINV LINV_cl HOWN w s LB LBs m mo c ins tbl ftbl TB spal s1 m1 mo1 (set_v3A c (b', ys, cap')) O_V3 pid pid' b (4 * cap) b' (4 * cap')
                  (closs cap cap') _ _ XS OK X Hknn Hfk ltac:(unfold O_V1, O_V3; lia) ltac:(unfold O_V3, PARSER_SIZE; lia));
          [ rewrite (cblocks_v3 c), EV3; cbn [t3a t3c fst snd]; reflexivity
          | rewrite cblocks_set_v3; replace (b' =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity
          | exact PIDin | lia | exact BUD1 | lia
          | reflexivity | reflexivity | reflexivity | reflexivity
          | exact RH1 | exact MP1 | exact MI1 | exact ST1 | exists errv1; exact ER1 | exact RA1 | exact FXS | exact XP1 | exact ABR1 | exact WV1 | exact RF1 | exact AC1' | exact S01
          | exact AL1
          | exact U1 | exact U2 | exact U3 | exact V1 | exact V2 | exact VEC1 | ].
        unfold set_v3A, pmc_sh. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3]. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|].
        split; [exact Z4|]. split; [exact Z5|].
        unfold vsh32. cbn [t3a t3b t3c fst snd]. intros _. apply SH1. lia. }
      eapply (K ms1 mo1 m1 _ s1 _ _ b' cap'); [exact KR1 | exact VIS1 | apply rfull_mkR | exact X1 | exact KEPT1 | exact HR0 | exact BUD1 | lia
                | right; split; [lia | exact ABR1] |].
      intros k cs Hk Hkc RWk.
      exact (vx_ff_keep H HHbp w s LB m m1 O_V3 b (4 * cap) pid XS k cs OK RH RF1 FXS ltac:(unfold O_V1, O_V3; lia) ltac:(unfold O_V3, PARSER_SIZE; lia) INbLB ltac:(lia) XP1 Hk Hkc RWk).
  Qed.

  Lemma pm_push_types : push_types_stmtA H ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (ret so sp_p : Z) (l : list Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AT_PUSH_TYPES) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + so) -> PropExec.getr R 11%bv = Z_to_bv 64 (wa_p w + O_V3) ->

    obj_sh_ok ins so 16 = true -> 24 <= so -> so + 16 <= 11584 -> so mod 8 = 0 ->
    rw_cells asegs m (wa_ff w + so) [C8 (Z_to_bv 64 sp_p); C8 (Z_to_bv 64 (Zlen l))] ->
    spanA sp_p l -> Zlen l <= 48 -> Forall (fun t => 0 <= t < 2 ^ 31) l ->

    (forall b'' xs'' cap'', 0 <= cap'' <= capmax (Zlen (t3b (c_v3 c))) (t3c (c_v3 c)) (Zlen l) -> pm_bud (wa_n w) (set_v3A c (b'', xs'', cap''))) ->
    trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] -> trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF] ->
    (forall msF1 mo1 m1 R1 (s1 : as_St H) (LB1 LBs1 : list block) (b' cap' : Z),
       as_AKREL H s1 (mkCfg msF1 mo1) ->
       as_VIS H s1 msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s1 LB1 LBs1 m1 mo1 (set_v3A c (b', push_types l (t3b (c_v3 c)), cap')) ins tbl ftbl TB spal ->
       (forall r, In r V4_KEPT -> PropExec.getr R1 r = PropExec.getr R r) ->
       pm_bud (wa_n w) (set_v3A c (b', push_types l (t3b (c_v3 c)), cap')) ->
       t3c (c_v3 c) <= cap' <= capmax (Zlen (t3b (c_v3 c))) (t3c (c_v3 c)) (Zlen l) ->
       ((b' = t3a (c_v3 c) /\ cap' = t3c (c_v3 c) /\ LB1 = LB /\ LBs1 = LBs) \/ (t3c (c_v3 c) < cap' /\ ablock_range H b' (4 * cap'))) ->
       (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
          rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros PT w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret so sp_p l Q OK X Hknn Hfk KR VIS RF
           G1 Hr2 Hr G2 G4 G10 G11 Hok Hso1 Hso2 Hso8 RW SPAN LL LR BUDm TRC TRR K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_frame_facts H w OK) as (E1 & E2 & E3 & _). change (fsz PM_FCLASS) with 16384 in *. unfold AIMG_TOP, AFS_HDR in E1.
    pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    destruct (p_frame H HH w OK) as (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4).
    pose proof (lf0_apart_ff H w fp0 (wa_p w) PARSER_SIZE OK Hfp0 PF1 PF2) as PFF. change (fsz PM_FCLASS) with 16384 in PFF.
    assert (ZL0 : 0 <= Zlen l) by (unfold Zlen; lia).
    eapply (pm_pat_call w s LB LBs m mo c ins tbl ftbl TB spal msF R F AT_PUSH_TYPES fc ret PT_STACK
              (capmax (Zlen (t3b (c_v3 c))) (t3c (c_v3 c)) (Zlen l)) (push_types l (t3b (c_v3 c))) (fun _ => True) Q
              OK X Hknn Hfk KR VIS RF G1 Hr2 Hr G2 G4);
      [unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK, APM_STACK; lia
      | unfold capmax; lia | exact BUDm | exact TRC | exact TRR | |].
    2:{ intros msF1 mo1 m1 R1 s1 LB1 LBs1 b' cap' KR1 VIS1 RF1 X1 KEPT1 _ BUD1 HC CASES FFK.
        eapply (K msF1 mo1 m1 R1 s1 LB1 LBs1 b' cap' KR1 VIS1 RF1 X1 KEPT1); [exact BUD1 | exact HC | exact CASES | exact FFK]. }
    intros pid errv PIDin PRE.
    rewrite (rfull_eq R RF) in VIS.
    eapply (PT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB (PMLF H w) (wa_ff w + so) sp_p (wa_p w + O_V3)
               (t3a (c_v3 c)) (t3c (c_v3 c)) l (t3b (c_v3 c)) pid (wa_lo w) (wa_B w) (wa_shi w) errv);
      [exact VIS | exact G10 | exact G11 | | clear - Hso8 E3; Z.div_mod_to_equations; lia
      | unfold O_V3, PARSER_SIZE in *; lia | exact SPAN | exact LL | exact LR
      | left; lia | exact (LINV_relro m (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)) | exact PRE].

    rewrite G2, u64_of_Z by lia.
    intros XS m' FXS AC' MI' XP.
    assert (INbLB : t3a (c_v3 c) <> 0 -> In (pid, t3a (c_v3 c), 4 * t3c (c_v3 c)) LB).
    { intros E. apply (Permutation_in _ (Permutation_sym OWN1)). apply in_or_app; right. apply in_or_app; left. exact (PIDin E). }
    destruct (ff_obj_keep H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal so [C8 (Z_to_bv 64 sp_p); C8 (Z_to_bv 64 (Zlen l))]
                ((wa_p w + O_V3, wa_p w + O_V3 + 24) :: v4_oldx (t3a (c_v3 c)) (4 * t3c (c_v3 c))) XS m'
                OK X ltac:(cbn [cells_size csize Nat.add]; exact Hok) Hso1 ltac:(cbn [cells_size csize Nat.add]; lia) RW) as (RW' & ACC' & _ & _);
      [| exact FXS | exact XP | split; [exact RW' | cbn [cells_size csize Nat.add] in ACC'; exact ACC']].
    unfold v4_oldx. apply Forall_cons; [cbn [fst snd]; unfold O_V3, PARSER_SIZE in *; split; [lia|] |].
    { pose proof (xp_geom H HH w OK) as (_ & _ & _ & _ & _ & FA & _). pose proof (wk_papp H w OK) as (PA & _).
      pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE (wa_ff w) 16384 PA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D.
      change (nsh 16384) with 2048 in D. unfold PM_NSH, PARSER_SIZE in *. clear - D. lia. }
    destruct (Z.eqb_spec (t3a (c_v3 c)) 0) as [E|E]; [apply Forall_nil|].
    pose proof (blk_apart_ff H HH w s LB m _ OK RH (INbLB E)) as BAF. cbn [blk_addr blk_size fst snd] in BAF. change (fsz PM_FCLASS) with 16384 in BAF.
    pose proof (blksh_apart_ff H HH w s LB m pid _ _ OK RH (INbLB E)) as [BSF BSFS].
    pose proof (ah_blocks H HH _ _ _ _ RH (INbLB E)) as (R0 & R16 & Rn & RI & RC & RFb & RAPP). cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RFb, RAPP.
    apply Forall_cons; [cbn [fst snd]; split; [lia|] | apply Forall_cons; [cbn [fst snd]; split; [exact BSF | exact BSFS] | apply Forall_nil]].
    pose proof (aapp_disjoint_sh (t3a (c_v3 c)) (4 * t3c (c_v3 c)) (wa_ff w) 16384 RAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D.
    change (nsh 16384) with 2048 in D. unfold PM_NSH in *. clear - D. lia.
  Qed.

  Lemma pm_take_first : take_first_stmtA H ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (ret : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AT_TAKE_FIRST) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_p w + O_V3) ->
    t3b (c_v3 c) <> [] -> Forall (fun t => 0 <= t < 2 ^ 31) (t3b (c_v3 c)) ->
    (forall b'' xs'' cap'', 0 <= cap'' <= capmax (Zlen (t3b (c_v3 c)) - 1) (t3c (c_v3 c)) 3 -> pm_bud (wa_n w) (set_v3A c (b'', xs'', cap''))) ->
    trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] -> trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF] ->
    (forall msF1 mo1 m1 R1 (s1 : as_St H) (LB1 LBs1 : list block) (b' cap' : Z),
       as_AKREL H s1 (mkCfg msF1 mo1) ->
       as_VIS H s1 msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s1 LB1 LBs1 m1 mo1 (set_v3A c (b', snd (take_first (t3b (c_v3 c))), cap')) ins tbl ftbl TB spal ->
       (forall r, In r V4_KEPT -> PropExec.getr R1 r = PropExec.getr R r) ->
       PropExec.getr R1 10%bv = Z_to_bv 64 (fst (take_first (t3b (c_v3 c)))) ->
       pm_bud (wa_n w) (set_v3A c (b', snd (take_first (t3b (c_v3 c))), cap')) ->
       t3c (c_v3 c) <= cap' <= capmax (Zlen (t3b (c_v3 c)) - 1) (t3c (c_v3 c)) 3 ->
       ((b' = t3a (c_v3 c) /\ cap' = t3c (c_v3 c) /\ LB1 = LB /\ LBs1 = LBs) \/ (t3c (c_v3 c) < cap' /\ ablock_range H b' (4 * cap'))) ->
       (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
          rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros TF w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret Q OK X Hknn Hfk KR VIS RF
           G1 Hr2 Hr G2 G4 G10 HNE LR BUDm TRC TRR K.
    eapply (pm_pat_call w s LB LBs m mo c ins tbl ftbl TB spal msF R F AT_TAKE_FIRST fc ret TF_STACK
              (capmax (Zlen (t3b (c_v3 c)) - 1) (t3c (c_v3 c)) 3) (snd (take_first (t3b (c_v3 c))))
              (fun r0 => r0 = Z_to_bv 64 (fst (take_first (t3b (c_v3 c))))) Q
              OK X Hknn Hfk KR VIS RF G1 Hr2 Hr G2 G4);
      [unfold TF_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK, APM_STACK; lia
      | unfold capmax; lia | exact BUDm | exact TRC | exact TRR | | ].
    - intros pid errv PIDin PRE.
      rewrite (rfull_eq R RF) in VIS.
      eapply (TF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB (PMLF H w) (wa_p w + O_V3)
                 (t3a (c_v3 c)) (t3c (c_v3 c)) (t3b (c_v3 c)) pid (wa_lo w) (wa_B w) (wa_shi w) errv);
        [exact VIS | exact G10 | exact HNE | exact LR | exact (LINV_relro m (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)) | exact PRE].
    - intros msF1 mo1 m1 R1 s1 LB1 LBs1 b' cap' KR1 VIS1 RF1 X1 KEPT1 HR0 BUD1 HC CASES FFK.
      eapply (K msF1 mo1 m1 R1 s1 LB1 LBs1 b' cap' KR1 VIS1 RF1 X1 KEPT1); [exact HR0 | exact BUD1 | exact HC | exact CASES | exact FFK].
  Qed.
End WPT.

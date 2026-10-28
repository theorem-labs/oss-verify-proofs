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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmVops LbB_PmDS LbB_WoGen LbB_ContStmt LbB_ContV4 LbB_PmWKit LbB_PmWG.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WV4.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis HOWN : rt_own H.

  Let HH : asan_rt_hyps H := proj1 HHbp.

  Lemma pmxa_vgrow2 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' (pid pid' : bptr) (b' x : Z),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    Zlen (t3b (c_v2 c)) = t3c (c_v2 c) ->
    (t3a (c_v2 c) <> 0 -> In (pid, t3a (c_v2 c), 4 * t3c (c_v2 c)) LBs) ->
    pm_bud (wa_n w) (set_v2A c (b', t3b (c_v2 c) ++ [x], vgrow (t3c (c_v2 c)))) ->

    as_RHEAP H s' (v4_newLB H LB (t3a (c_v2 c)) pid pid' b' (4 * vgrow (t3c (c_v2 c)))) m' -> as_MPRES H mo mo' -> mem_inv asegs m' ->
    stk asegs m' (wa_lo w) (wa_s1 w) -> (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) ->
    as_rauxv_ok H m' (wa_B w) ->
    xpres H LB (wa_s1 w) ((wa_p w + O_V2, wa_p w + O_V2 + 24) :: v4_oldx (t3a (c_v2 c)) (4 * t3c (c_v2 c))) m m' ->
    ablock_range H b' (4 * vgrow (t3c (c_v2 c))) ->
    vec32A (v4_newLB H LB (t3a (c_v2 c)) pid pid' b' (4 * vgrow (t3c (c_v2 c)))) m' (wa_p w + O_V2) b' (t3b (c_v2 c) ++ [x]) (vgrow (t3c (c_v2 c))) ->
    SHAD m' b' (cc_gen (4 * vgrow (t3c (c_v2 c))) (4 * (t3c (c_v2 c) + 1))) ->
    wr_at asegs m' (wa_p w + O_V2) 24 ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) ->
    as_AL H s' >= as_AL H s - (as_Cm H (4 * vgrow (t3c (c_v2 c))) + as_Cf H (4 * t3c (c_v2 c))) ->
    PMXAT H LINV w s' (v4_newLB H LB (t3a (c_v2 c)) pid pid' b' (4 * vgrow (t3c (c_v2 c))))
          ((pid', b', 4 * vgrow (t3c (c_v2 c))) :: (if t3a (c_v2 c) =? 0 then LBs else as_lb_remove H pid LBs)) m' mo'
          (set_v2A c (b', t3b (c_v2 c) ++ [x], vgrow (t3c (c_v2 c)))) ins tbl ftbl TB spal.
Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' pid pid' b' x OK X0 Hknn Hfk FULL PIDin BUDc
           RH' MP' MI' STK' ERR' RA' XP ABR' V2' SH' WR' RFS' AC' S0' AL'.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    pose proof (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as V2.
    destruct (c_v2 c) as [[b xs] cap] eqn:EV2. cbn [t3a t3b t3c fst snd] in *.
    pose proof V2 as (Hv & Hv' & HD & Hlen & Hb & _).
    assert (Hcap0 : 0 <= cap) by (unfold Zlen in *; lia).
    assert (B0C : b = 0 -> cap = 0) by (intros B0; destruct Hb as [[_ C0]|(Bp & _)]; lia).
    set (cap' := vgrow cap) in *. set (n' := 4 * cap') in *.
    set (LB' := v4_newLB H LB b pid pid' b' n') in *.
    set (c' := set_v2A c (b', xs ++ [x], cap')) in *.
    destruct (rt_bp_cost H HHbp) as [CFz CMz]. rewrite CFz, CMz, Z.add_0_r in AL'.

    destruct (pmxa_keep_but_xp H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal m' (lbl LB') (vx H w O_V2 b (4 * cap)) [] O_V2 (b, 4 * cap)
                OK X0 RFS' ltac:(apply Forall_nil) ltac:(rewrite app_nil_r; exact XP) (vx_vwin H w O_V2 b (4 * cap) ltac:(lia)) ltac:(unfold O_V1, O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia)
                ltac:(right; left; split; [reflexivity | unfold blkV2; rewrite EV2; reflexivity]))
      as (U1 & U2 & U3 & S1 & S2 & S3 & K1 & _ & K3).
    { intros q Hq Hne Hl. eapply (vgrow_live H HHbp w s LB LBs TB m c pid pid' b (4 * cap) b' n' (b, 4 * cap) q OK RH OWN1 OWN2 eq_refl PIDin Hq Hne Hl). }
    destruct (K1 ltac:(unfold O_V1, O_V2; lia)) as [V1 S4]. destruct (K3 ltac:(unfold O_V2, O_V3; lia)) as [V3 S6].

    pose proof ABR' as (B'0 & _).
    pose proof (phi_grow_v2 c b' (xs ++ [x]) cap ltac:(rewrite EV2; reflexivity) Hcap0 ltac:(rewrite EV2; cbn [t3a fst snd]; exact B0C) ltac:(lia)) as PG.
    fold cap' in PG. change (set_v2A c (b', xs ++ [x], cap')) with c' in PG. fold n' in PG.
    eapply (pmxa_vgrow_gen H HHbp LINV LINV_cl HOWN w s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' c' O_V2 pid pid' b (4 * cap) b' n' (ICM n')
              _ _ [] OK X0 Hknn Hfk ltac:(unfold O_V1, O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia));
      [ rewrite (cblocks_v2 c), EV2; cbn [t3a t3c fst snd]; reflexivity
      | unfold c'; rewrite cblocks_set_v2; replace (b' =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity
      | exact PIDin | lia | exact BUDc | exact PG
      | reflexivity | reflexivity | reflexivity | reflexivity
      | exact RH' | exact MP' | exact MI' | exact STK' | exact ERR' | exact RA' | apply Forall_nil | rewrite app_nil_r; exact XP | exact ABR' | exact WR' | exact RFS' | exact AC' | exact S0' | exact AL'
      | exact U1 | exact U2 | exact U3 | exact V1 | exact V2' | exact V3 | ].
    subst c'. unfold set_v2A, pmc_sh. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
    split; [exact S4|]. split; [|exact S6].
    unfold vsh32. cbn [t3a t3b t3c fst snd]. intros _.
    replace (4 * Zlen (xs ++ [x])) with (4 * (cap + 1)) by (unfold Zlen in *; rewrite length_app; cbn [length]; lia). exact SH'.
  Qed.

  Lemma pm_v4slow2 : forall (cc : v4_consts), v4slow_stmt H cc ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (ret so x : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 (v4_entry cc)) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_p w + O_V2) -> PropExec.getr R 11%bv = Z_to_bv 64 (wa_ff w + so) ->

    Zlen (t3b (c_v2 c)) = t3c (c_v2 c) ->
    obj_sh_ok ins so 4 = true -> 24 <= so -> so + 4 <= 16376 -> so mod 4 = 0 ->
    rw_cells asegs m (wa_ff w + so) [C4 (Z_to_bv 64 x)] -> 0 <= x < 2 ^ 32 -> x < v4_xmax cc ->

    (forall b'' xs'', pm_bud (wa_n w) (set_v2A c (b'', xs'', vgrow (t3c (c_v2 c))))) ->
    trace_ok (as_TR H) APC0_FREE [v4_del_ra cc] ->
    (forall msF1 mo1 m1 R1 (s1 : as_St H) (pid pid' : bptr) (b' : Z),
       as_AKREL H s1 (mkCfg msF1 mo1) ->
       as_VIS H s1 msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s1 (v4_newLB H LB (t3a (c_v2 c)) pid pid' b' (4 * vgrow (t3c (c_v2 c))))
             ((pid', b', 4 * vgrow (t3c (c_v2 c))) :: (if t3a (c_v2 c) =? 0 then LBs else as_lb_remove H pid LBs)) m1 mo1
             (set_v2A c (b', t3b (c_v2 c) ++ [x], vgrow (t3c (c_v2 c)))) ins tbl ftbl TB spal ->
       (forall r, In r V4_KEPT -> PropExec.getr R1 r = PropExec.getr R r) ->
       PropExec.getr R1 10%bv = Z_to_bv 64 (b' + 4 * (t3c (c_v2 c) + 1)) ->
       ablock_range H b' (4 * vgrow (t3c (c_v2 c))) -> pm_bud (wa_n w) (set_v2A c (b', t3b (c_v2 c) ++ [x], vgrow (t3c (c_v2 c)))) ->
       (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
          rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
Proof.
    intros cc V4 w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret so x Q OK X Hknn Hfk KR VIS RF
           G1 Hr2 Hr G2 G4 G10 G11 XSL Hok Hso1 Hso2 Hso4 RW Hx Hxm BUD' TRd K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16). pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (wk_s1 H w OK) as [T1 T2].
    pose proof (wk_n H w OK) as WN.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as V2.
    pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (SHc & ADp & _).
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (A1 & A2 & A3 & A4).
    destruct (c_v2 c) as [[b xs] cap] eqn:EV2. cbn [t3a t3b t3c fst snd] in *.
    pose proof V2 as (Hv & Hv' & HD & Hlen & Hb & _).
    assert (Hcap0 : 0 <= cap) by (unfold Zlen in *; lia).
    assert (B0C : b = 0 -> cap = 0) by (intros B0; destruct Hb as [[_ C0]|(Bp & _)]; lia).
    set (cap' := vgrow cap) in *.
    assert (VG : cap' >= 2 * cap /\ cap' >= cap + 1) by (unfold cap', vgrow; lia).

    assert (OLD : exists pid, v4_oldblk LB b cap pid /\ (b <> 0 -> In (pid, b, 4 * cap) LBs)).
    { destruct (Z.eq_dec b 0) as [E|E].
      - exists 0. split; [left; split; [exact E | exact (B0C E)] | intros NZ; contradiction].
      - destruct (cblk_facts H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal b (4 * cap) OK X) as (pid & I1 & I2 & _).
        { rewrite (cblocks_v2 c), EV2. cbn [t3a t3c fst snd]. rewrite !in_app_iff. right; left.
          destruct (Z.eqb_spec b 0); [contradiction | left; reflexivity]. }
        exists pid. split; [right; split; [destruct Hb as [[B0 _]|(Bp & _ & Cp & _)]; [contradiction | exact Cp] | exact I2] | intros _; exact I1]. }
    destruct OLD as (pid & OB & PIDin).
    assert (INbLB : b <> 0 -> In (pid, b, 4 * cap) LB).
    { intros E. apply (Permutation_in _ (Permutation_sym OWN1)). apply in_or_app; right. apply in_or_app; left. exact (PIDin E). }

    destruct (rt_bp_cost H HHbp) as [CFz CMz].
    assert (FULLf : 4 * cap' <= 2 ^ 26 /\ ICM (4 * cap') <= as_AL H s).
    { set (c'0 := set_v2A c (1, [], cap')).
      assert (BUD0 : pm_bud (wa_n w) c'0) by (unfold c'0; apply BUD').
      pose proof (pm_resv_of_bud (wa_n w) c'0 WN BUD0) as RESV0.
      pose proof (phi_grow_v2 c 1 [] cap ltac:(rewrite EV2; reflexivity) Hcap0 ltac:(rewrite EV2; cbn [t3a fst snd]; exact B0C) ltac:(lia)) as PG. fold cap' c'0 in PG.
      pose proof (pm_phi_le_cap c'0) as PC0.
      pose proof BUD0 as (_ & _ & _ & _ & _ & Bv2 & _). unfold c'0, set_v2A in Bv2. cbn [c_v2 t3c snd] in Bv2. lia. }
    pose proof (pmxa_meas_LB H LINV w s LB LBs m mo c ins tbl ftbl TB spal OK X) as (M1 & M2 & M3).
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H HH).
    { eapply V4 with (v := wa_p w + O_V2) (b := b) (cap := cap) (src := wa_ff w + so) (x := x) (xs := xs) (pid := pid)
        (LB := LB) (LF := PMLF H w) (lo := wa_lo w) (B := wa_B w) (shi := wa_shi w) (errv := errv) (s := s) (m := m) (mo := mo);
      [ exact VIS | exact G10 | exact G11
      | unfold vec32A; exact V2 | exact XSL | unfold O_V2; Z.div_mod_to_equations; lia
      | apply (pw_addr_sub8 m (wa_p w) PARSER_SIZE O_V2 24 ADp); unfold O_V2, PARSER_SIZE; try reflexivity; lia
      | rewrite G2, u64_of_Z by lia; apply (pwin_obj H HH w LB O_V2 OK); unfold O_V2, PARSER_SIZE; try reflexivity; lia
      | exact (proj1 (pwin_band H w (wa_p w + O_V2) 24 OK ltac:(unfold O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia) ltac:(lia)))
      | apply (wr_at_of_mdef m (wa_p w) PARSER_SIZE O_V2 24 (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)); unfold O_V2, PARSER_SIZE; lia
      | exact (HOWN s LB m RH)
      | exact OB
      | intros Cp; pose proof SHc as (_ & _ & _ & _ & SH5 & _); rewrite EV2 in SH5; unfold vsh32 in SH5; cbn [t3a t3b t3c fst snd] in SH5;
          rewrite XSL in SH5; apply SH5; lia
      | unfold v4_newcap; fold cap'; exact (proj1 FULLf)
      | rewrite G2, u64_of_Z by lia; exact (ff_src4_keep H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal so x OK X Hok Hso1 Hso2 RW Hx)
      | lia | Z.div_mod_to_equations; lia | lia | lia
      | exact RH | exact KR
      | apply (rt_bp_live H HHbp s LB m (4 * v4_newcap cap) RH); unfold v4_newcap; fold cap';
          [lia | unfold nsmall; destruct (Z.leb_spec (4 * cap') 64512); lia | lia | unfold nlg; destruct (Z.ltb_spec 64512 (4 * cap')); lia]
      | rewrite CFz, CMz; unfold v4_newcap; fold cap'; pose proof (proj2 FULLf); lia
      | exact TRd
      | exact (xa_rauxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | rewrite G2, u64_of_Z by lia; lia
      | rewrite G2, u64_of_Z by lia; Z.div_mod_to_equations; lia | rewrite G2, u64_of_Z by lia; lia
      | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia)))
      | lia | rewrite G2, u64_of_Z by lia; unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK, APM_STACK in *; lia
      | rewrite G4; exact ERR | exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | rewrite G4; exact (wk_tp H w OK)
      | rewrite G1, u64_of_Z by lia; exact Hr2
      | exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
      | rewrite G2, u64_of_Z by lia; lia ]. }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & pid' & b' & POST).
    cbv zeta in POST.
    destruct POST as (VIS1 & KR1 & MP1 & MI1 & ST1 & ER1 & RA1 & XP1 & ABR1 & RH1 & VEC1 & SH1 & AD1 & WV1 & OW1 & RF1 & AC1' & S01 & AL1).
    cbn [cfg_ms cfg_model] in VIS1, KR1, MP1.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in ST1 by lia. rewrite G4 in ER1.
    rewrite G2, u64_of_Z in XP1 by lia.
    assert (X1 : PMXAT H LINV w s1 (v4_newLB H LB b pid pid' b' (4 * cap')) ((pid', b', 4 * cap') :: (if b =? 0 then LBs else as_lb_remove H pid LBs)) m1 mo1
                   (set_v2A c (b', xs ++ [x], cap')) ins tbl ftbl TB spal).
    { pose proof (pmxa_vgrow2 w s LB LBs m mo c ins tbl ftbl TB spal s1 m1 mo1 pid pid' b' x OK X Hknn Hfk) as VGR.
      rewrite EV2 in VGR. cbn [t3a t3b t3c fst snd] in VGR. fold cap' in VGR.
      apply VGR; [exact XSL | exact PIDin | apply BUD' | exact RH1 | exact MP1 | exact MI1 | exact ST1 | exists errv1; exact ER1 | exact RA1
              | exact XP1 | exact ABR1 | exact VEC1 | exact SH1 | exact WV1 | exact RF1 | exact AC1' | exact S01 | exact AL1]. }
    eapply (K ms1 mo1 m1 _ s1 pid pid' b'); [exact KR1 | exact VIS1 | apply rfull_mkR | exact X1 | | | exact ABR1 | apply BUD' |].
    + intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    + first [reflexivity | (cbn; reflexivity)].
    + intros k cs Hk Hkc RWk.
      exact (vx_ff_keep H HHbp w s LB m m1 O_V2 b (4 * cap) pid [] k cs OK RH RF1 ltac:(apply Forall_nil) ltac:(unfold O_V1, O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia) INbLB ltac:(lia) ltac:(rewrite app_nil_r; exact XP1) Hk Hkc RWk).
  Qed.
End WV4.

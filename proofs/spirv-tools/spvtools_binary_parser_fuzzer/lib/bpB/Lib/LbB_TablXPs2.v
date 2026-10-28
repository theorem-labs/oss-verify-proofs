(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_DStat LbB_ContStmt LbB_ContV4 LbB_ContVot LbB_TablStmt LbB_TablOS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_RGl LbB_TablPT4 LbB_TablPT5 LbB_TablPT6 LbB_TablPT8 LbB_TablPT9 LbB_TablPT11 LbB_TablXP1 LbB_TablXPk1 LbB_TablXPk2 LbB_TablXPs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section XPs2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Lemma xstep_slow : forall s (e : xpent H) ys sv msF mo (Q : config -> Prop) R mL sL LBi bi capi pidi eL,
    xs_wf s -> site_runs s -> v4slow_stmt H (xs_c s) -> xpre H e -> XV e ->
    (xs_setslots s = true -> x_t e = xs_lit s) -> (xs_setslots s = false -> sv = Some (xs_sv s)) ->
    Zlen ys + 1 <= Zlen (x_xs e) + 3 ->
    as_VIS H sL msF = MS R (x_F e) (Z_to_bv 64 (xs_pc s)) (x_fc e) None mL (seg_rom asegs) -> rfull R ->
    getr R 3 = x_gp e -> getr R 4 = x_tp e -> RPl (xcommon (xg e bi capi ys) ++ xs_rin s (xg e bi capi ys)) R ->
    as_AKREL H sL (mkCfg msF mo) -> as_MPRES H (x_mo e) mo ->
    xmem H e ys sv mL sL LBi bi capi pidi eL -> Zlen ys = capi ->
    (forall cf', xat H e (xs_nx s) (fun g => xs_rout s g (g_e g)) (ys ++ [xs_lit s]) (Some (xs_sv s)) cf' -> as_SR H Q cf') ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros s e ys sv msF mo Q R mL sL LBi bi capi pidi eL WF RUNS VS P XVH HT HSV YL VIS HF G3 G4 RP KR MP PM LCeq K.
    pose proof (rt_bp_base H HH) as HB.
    destruct RUNS as (RA & _ & RC).
    destruct PM as (PF & SL & PV & XP & AL).
    pose proof PF as (MI & AC & ST & _ & _ & _ & _ & CL & _ & WF256 & WS32 & _ & _ & KC & _ & RH & _).
    pose proof P as (_ & _ & _ & _ & _ & SPB & SPS & _ & _ & _ & RA0 & _ & TRO2 & _ & _ & _ & _ & _ & _ & OBJ & _ & _ & RH0 & _ & _ & _ & _ & TRO & AL0 & _).
    pose proof (xgeoP_of H e P) as G.
    destruct G as (SP16 & S45 & S132 & S1S & S1L & SPH & CEl & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & _ & FS2 & _ & SHF1 & SHF2 & _ & FB & _
                   & V8 & VB & VL & VF & _ & _ & SV1 & SV2 & TR & TP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    destruct (xvec_blk H HB e ys mL sL LBi bi capi pidi RH PV) as (LEN & BK & DJV).
    pose proof PV as (VEC & SH & AD & WV & OB & GR).
    destruct (xcap_bound H e LBi bi capi pidi P XVH GR) as (CB1 & CB2 & CB3).
    pose proof (vgrow_ge capi ltac:(lia)) as VG.
    assert (CM' : v4_newcap capi <= xcapm e).
    { revert XVH CB1 CB2 LCeq YL LEN. clear. unfold XV, v4_newcap, xcapm, capmax, vgrow. destruct (PrsGrammar.expand (x_t e)); [lia | intros X; exfalso; exact (X eq_refl)]. }
    assert (VM : vgrow capi <= xcapm e) by (unfold v4_newcap in CM'; exact CM').
    assert (BR : 0 <= bi /\ bi + 4 * capi <= aceil).
    { destruct BK as [(C0 & B0)|(C0 & HIn & (A0 & _ & _ & _ & ACe & _))]; [subst; lia | lia]. }
    pose proof (xg_ok_of H HH e ys mL sL LBi bi capi pidi P RH PV) as GOK.
    pose proof VEC as (_ & _ & _ & _ & _ & F0 & F8 & F16 & _).
    assert (GZ : gz mL (x_v e) 24) by (intros j Hj; eapply sh0_of_addressable; [exact AD | change (8 * (24 / 8)) with 24; lia]).
    assert (W16 : wr_at asegs mL (xS1 e + 16) 16).
    { pose proof (wr_at_of_stk asegs mL (x_lo e) (xSP e) ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (xS1 e + 16 + i) with (x_lo e + (xS1 e + 16 - x_lo e + i)) by lia. apply W. lia. }
    assert (W128 : wr_at asegs mL (x_ff e + 32) 128) by (eapply vt_wr_sub; [exact WF256 | lia | lia | lia]).
    assert (SLc : xs_setslots s = false -> xslotc (xs_sv s) (xg e bi capi ys) mL).
    { intros E0. rewrite (HSV E0) in SL. exact SL. }

    destruct (RA R (x_F e) (x_fc e) mL (seg_rom asegs) (xg e bi capi ys) RP GOK F0 F8 F16 GZ W16 SLc WS32 W128)
      as (R1 & M1 & pc1 & RUN1 & K13 & K14 & MU1 & WM1 & SK1 & MI1 & SL1 & SRC1 & TK1 & PK1 & BR1).
    cbn [g_e g_c g_b g_v g_ff g_S1 g_SP xg] in BR1.
    replace (bi + 4 * Zlen ys <? bi + 4 * capi) with false in BR1 by (symmetry; apply Z.ltb_ge; lia).
    destruct BR1 as (Epc & L1 & L10 & L11 & RP1). subst pc1.
    destruct (xwa_ok H HH s e LBi bi capi ys WF P) as (OKA & FRA & XEA).
    assert (PF1 : xframe H e M1 sL LBi eL).
    { eapply (xframe_munch H HB e mL M1 sL LBi eL); [exact P | exact PF | exact MU1 | exact WM1 | exact (MI1 MI) | exact (SK1 _ _ ST) | exact OKA]. }
    pose proof (xvec_frm H HB e ys mL M1 sL LBi bi capi pidi _ P RH PV MU1 WM1 FRA) as PV1.
    assert (XP1 : xpres H (x_LB e) (xSP e) (xXE H e) (x_m e) M1).
    { eapply (xpres_trans H); [exact XP|].
      eapply (xpres_of_munch H (x_s e) (x_LB e) (xSP e) (xXE H e) _ (x_m e) mL M1); [exact HB | exact RH0 | exact MU1 | exact WM1 | exact XEA]. }
    clear PF SL PV XP MU1 WM1 SK1 MI1 GZ W16 W128 SLc.
    eapply (sr_blk H HB); [exact KR | exact VIS | exact HF | exact RUN1 |].
    intros msF1 mo1 KR1 MP1 VIS1.
    destruct PV1 as (VEC1 & SH1 & AD1 & WV1 & OB1 & _).
    pose proof PF1 as (MI1 & AC1 & ST1 & S01 & ER1 & RA1 & _ & CL1 & _ & _ & WS1 & _ & _ & KC1 & RF1 & RH1 & OW1).
    pose proof WF as WF'. vhide WF'. destruct WF as (WC & WL & WSS1 & WSS2 & WPK & WFK & WTK & WRO & WMID & WMID' & SRA & SRA2 & ARA & ARA2).
    pose proof (RPl_sp _ _ _ RP1) as Q2. cbn [g_S1 xg] in Q2.
    assert (T4 : getr R1 4 = x_tp e) by (rewrite K14; exact G4).
    assert (T3 : getr R1 3 = x_gp e) by (rewrite K13; exact G3).

    assert (SK4 : src4_keep H LBi (xS1 e) M1 (x_ff e + xs_src s) (xs_lit s)).
    { destruct (xs_setslots s) eqn:ES.
      - rewrite (WSS1 eq_refl). replace (x_ff e + 32) with (x_ff e + 8 * 4) by lia.
        apply (x_src_keep H e LBi (xS1 e) M1 4 (xs_lit s) P ltac:(lia) ltac:(lia)); [| exact KC1 | lia].
        replace (x_ff e + 8 * 4) with (x_ff e + 32) by lia. rewrite <- (HT eq_refl). exact CL1.
      - destruct (WSS2 eq_refl) as (SRC & TKa & TKb). rewrite SRC.
        apply (x_src_keep H e LBi (xS1 e) M1 (xs_tk s) (xs_lit s) P ltac:(lia) ltac:(lia)); [| | lia].
        + rewrite <- SRC. exact (SRC1 eq_refl).
        + unfold fkc in TK1. cbn [g_ff xg] in TK1. exact (TK1 ltac:(lia)). }
    assert (TROc : trace_ok (as_TR H) APC0_FREE [v4_del_ra (xs_c s)]) by (destruct WC as [-> | ->]; [exact TRO | exact TRO2]).
    assert (XL32 : 0 <= xs_lit s < v4_xmax (xs_c s))
      by (destruct WC as [-> | ->]; unfold VOT_SLOW_CREF, VOT_SLOW_RREF; cbn [v4_xmax]; clear - WL; lia).
    clear WC WPK WTK WRO WMID ARA ARA2 TRO TRO2.
    pose proof (xgrown_blocks H HB e LBi bi capi pidi P GR) as BL.
    assert (OBJ1 : obj_win H LBi (xLF e) (xS1 e) (x_lo e) (x_v e) 24).
    { pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                       & CX & B0C & BB & BD).
      eapply (pt_objwin_LBi H (x_LB e) LBi (x_LF e) (xLF e) (xSP e) (xS1 e) (x_lo e) (x_v e) (x_b e) (4 * x_cap e) OBJ);
        [ lia | destruct VL; [left | right]; lia
        | intros bb Hb; destruct (BL bb Hb) as [IN|(EQ & _)]; [left; exact IN | right; subst bb; cbn; split; reflexivity]
        | intros f Hf; right; exact Hf | destruct VB; lia | exact V8 | destruct BB; lia
        | destruct (Z.eq_dec (x_b e) 0) as [E|E]; [rewrite E; reflexivity | ]
        | lia | destruct BB; lia | destruct VB; [left | right]; lia
        | destruct (Z.eq_dec (x_b e) 0) as [E|E]; [right; pose proof (B0C E); lia | exact (BD E)]
        | destruct BB; [left | right]; lia | destruct VB; lia ].
      pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & _).
      destruct OLD as [(X & _)|(C0 & HIn0)]; [contradiction|].
      pose proof (ah_blocks H HB _ _ _ _ RH0 HIn0) as (_ & A16 & _). cbn [blk_addr fst snd] in A16.
      clear - A16; Z.div_mod_to_equations; lia. }
    destruct (x_budget H HB e LBi bi capi pidi P XVH GR ltac:(clear - LEN; lia)) as (BU1 & BU2 & BU3).
    destruct (rt_bp_cost H HH) as [CFz CMz].
    assert (NC64 : 4 * v4_newcap capi <= 2 ^ 26) by (clear - CB2 CM'; lia).
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GC' & _).
    pose proof (proj2 (GC' XVH)) as GC.
    pose proof (closs_step_ICM capi ltac:(clear - LEN; lia)) as CS1. pose proof (closs_mono capi (vgrow capi) (xcapm e) VM) as CS2.
    pose proof (closs_tele (x_cap e) capi (xcapm e)) as CS3. pose proof (closs_tele (x_cap e) capi (vgrow capi)) as CS4.
    assert (SRCr : (x_ff e + xs_src s) mod 4 = 0 /\ 0 <= x_ff e + xs_src s /\ x_ff e + xs_src s + 4 <= 2 ^ 47).
    { destruct (xs_setslots s).
      - rewrite (WSS1 eq_refl). clear - F64 FL FH ACF2. split; [Z.div_mod_to_equations; lia | lia].
      - destruct (WSS2 eq_refl) as (-> & X & Y). clear - F64 FL FH ACF2 X Y. split; [Z.div_mod_to_equations; lia | lia]. }
    destruct SRCr as (SRC4 & SRC0 & SRC47).
    assert (US1 : bv_unsigned (Z_to_bv 64 (xS1 e)) = xS1 e) by (apply u64_of_Z; clear - S45 SPH S1S; lia).
    assert (COST : as_Cm H (4 * v4_newcap capi) + as_Cf H (4 * capi) <= as_AL H sL).
    { rewrite CFz, CMz. unfold v4_newcap. clear - CS1 CS2 CS3 GC AL. lia. }
    destruct (stk_split asegs M1 (x_lo e) (xS1 e) (xSP e) ST1 ltac:(clear - LO CEl S1S; lia)) as [ST1l ST1u].
    assert (S116 : xS1 e mod 16 = 0) by (clear - S132; Z.div_mod_to_equations; lia).
    assert (LOV : x_lo e <= xS1 e - V4_STACK) by (clear - LO; unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK; lia).
    assert (RA1' : getr R1 1 = Z_to_bv 64 (xs_sra s)) by exact L1.
    eapply (ah_seq H HB).
    { eapply VS with (v := x_v e) (b := bi) (cap := capi) (src := x_ff e + xs_src s) (x := xs_lit s) (xs := ys) (pid := pidi)
        (LB := LBi) (LF := xLF e) (lo := x_lo e) (B := x_B e) (shi := x_shi e) (errv := eL);
      [ exact VIS1 | exact L10 | exact L11 | exact VEC1 | exact LCeq | exact V8 | exact AD1
      | rewrite Q2, US1; exact OBJ1
      | exact VB | exact WV1 | exact OW1 | exact OB1
      | intros Hc; pose proof (SH1 Hc) as X; rewrite LCeq in X; exact X
      | clear - NC64; lia
      | rewrite Q2, US1; exact SK4
      | exact XL32 | exact SRC4 | exact SRC0 | exact SRC47
      | exact RH1 | exact KR1
      | apply (rt_bp_live H HH sL LBi M1 (4 * v4_newcap capi) RH1); [clear - NC64 VG; unfold v4_newcap in *; lia | exact BU1 | exact BU2 | exact BU3]
      | exact COST
      | exact TROc | exact RA1 | rewrite Q2, US1; clear - SPB S1S; lia
      | rewrite Q2, US1; exact S116
      | rewrite Q2, US1; clear - SPH S1S; lia
      | rewrite Q2, US1; exact ST1l
      | exact CEl | rewrite Q2, US1; exact LOV
      | rewrite T4; exact ER1 | exact MI1 | rewrite T4; exact TP
      | rewrite RA1', u64_of_Z by (clear - SRA; lia); exact SRA2
      | exact AC1 | exact RF1 | exact S01 | rewrite Q2, US1; clear - SPS S1S; lia ]. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv' & s' & pid' & b' & POST).
    cbv zeta in POST.
    destruct POST as (VIS2 & KR2 & MP2 & MI2 & ST2 & ER2 & RA2 & XP2 & ABR2 & RH2 & VEC2 & SH2 & AD2 & WV2 & OW2 & RF2 & AC2 & S02 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite L1 in VIS2. rewrite (ret_pc_even (xs_sra s) ltac:(lia) SRA2) in VIS2.
    rewrite Q2, US1 in ST2, XP2. rewrite T4 in ER2.
    set (cap' := v4_newcap capi) in *. set (LBi' := v4_newLB H LBi bi pidi pid' b' (4 * cap')) in *.
    assert (BK' : bi = 0 /\ capi = 0 \/ (0 < capi /\ ablock_range H bi (4 * capi))).
    { destruct BK as [(C0 & B0)|(C0 & HIn & ABR)]; [left; split; assumption | right; split; assumption]. }
    destruct (xframe_v4 H e M1 m2 sL s' LBi LBi' bi capi eL errv' P PF1 BK' MI2 AC2 ST2 S02 ER2 RA2 RF2 RH2 OW2 XP2) as [PF2 SLK].
    pose proof (SLK (Some (xs_sv s)) SL1) as SL2. cbn [xslotP] in SL2.

    assert (CP' : capi + 1 <= cap') by (unfold cap', v4_newcap; lia).
    assert (GR' : xgrown H e LBi' b' cap' pid').
    { right. split; [lia|]. split; [|exact ABR2].
      unfold LBi'. exact (x_newLB_eq H HB e LBi bi capi pidi pid' b' (4 * cap') P GR (ah_nodup H HB _ _ _ RH1)). }

    assert (XP12 : xpres H (x_LB e) (xSP e) (xXE H e) M1 m2).
    { destruct GR as [(E1 & E2 & E3 & E4)|(GG1 & GG2 & GG3)].
      - rewrite E2, E1, E3 in XP2.
        eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hb; exact Hb |].
        intros a Ha. unfold xXE. cbn [rin_ivs] in Ha |- *. destruct Ha as [Ha|Ha]; [left; exact Ha | right; apply rin_ivs_app; left; exact Ha].
      - destruct (xgrown_tail H HB e LBi bi capi pidi P GG2) as (LBt & EL & BLt).
        rewrite EL in XP2, RH1.
        assert (NI : ~ In pidi (map blk_id LBt)).
        { pose proof (ah_nodup H HB _ _ _ RH1) as NDi. cbn [map] in NDi. apply NoDup_cons_iff in NDi as [X _]. exact X. }
        assert (B0 : bi <> 0) by (pose proof GG3 as (A0 & _); lia).
        assert (XE : v4_oldx bi (4 * capi) = [(bi, bi + 4 * capi); (sh bi, sh bi + nsh (4 * capi))])
          by (unfold v4_oldx; destruct (Z.eqb_spec bi 0); [contradiction | reflexivity]).
        rewrite XE in XP2.
        change ((x_v e, x_v e + 24) :: [(bi, bi + 4 * capi); (sh bi, sh bi + nsh (4 * capi))])
          with ([(x_v e, x_v e + 24)] ++ [(bi, bi + 4 * capi); (sh bi, sh bi + nsh (4 * capi))]) in XP2.
        pose proof (pt_xp_drop H HB sL LBt pidi bi (4 * capi) (xS1 e) [(x_v e, x_v e + 24)] M1 M1 m2 RH1 NI ltac:(lia) XP2) as XP3.
        eapply (pt_xp_lift H LBt (xS1 e) [(x_v e, x_v e + 24)] (x_LB e) (xSP e) (xXE H e) M1 m2 XP3 ltac:(lia)).
        + intros bb Hb. destruct (BLt bb Hb) as [IN|(EQ & Cc & Bc)]; [left; exact IN|]. right. intros a Ha. subst bb.
          cbn [blk_addr blk_size fst snd] in Ha. apply (xXE_old H); assumption.
        + intros a Ha. cbn [rin_ivs] in Ha. destruct Ha as [Ha|[]]. unfold xXE. cbn [rin_ivs]. left. exact Ha. }
    clear XP2.

    pose proof PF2 as (_ & _ & ST2f & _ & _ & _ & _ & _ & _ & _ & WS2f & _ & _ & _ & _ & RH2' & _).
    set (R3 := mkR (Z_to_bv 64 (xs_sra s)) (getr R1 2) (getr R1 3) (getr R1 4) t0' t1' t2' (getr R1 8) (getr R1 9)
                   (Z_to_bv 64 (b' + 4 * (capi + 1))) a1' a2' a3' a4' a5' a6' a7'
                   (getr R1 18) (getr R1 19) (getr R1 20) (getr R1 21) (getr R1 22) (getr R1 23) (getr R1 24) (getr R1 25)
                   (getr R1 26) (getr R1 27) t3' t4' t5' t6') in VIS2.
    assert (HF3 : rfull R3) by apply rfull_mkR.
    assert (RP3 : RPl (xcommon (xg e bi capi ys) ++ xs_rmid' s (xg e bi capi ys)) R3).
    { apply RPl_mkR; [|exact RP1]. apply Forall_app. split; [apply xcommon_XCS | apply WMID']. }
    assert (L10c : getr R3 10 = Z_to_bv 64 (b' + 4 * (capi + 1))) by reflexivity.
    pose proof ABR2 as (B'0 & B'16 & B'n & B'I & B'C & B'F & B'P).
    destruct (RC R3 (x_F e) (x_fc e) m2 (seg_rom asegs) (xg e bi capi ys) (b' + 4 * (capi + 1)) RP3 L10c GOK ltac:(lia) ltac:(lia)
                ltac:(clear - B'16; Z.div_mod_to_equations; lia) SL2
                ltac:(cbn [g_v xg]; eapply sh0_of_addressable; [exact AD2 | change (8 * (24 / 8)) with 24; lia])
                ltac:(cbn [g_v xg]; eapply vt_wr_sub; [exact WV2 | lia | lia | lia]) ltac:(cbn [g_ff xg]; exact WS2f))
      as (R4 & M3 & RUN3 & K43 & K44 & MU3 & WM3 & SK3 & MI3 & CV3 & FK3 & RP4).
    cbn [g_e g_v g_ff g_S1 g_SP g_b g_c xg] in MU3, CV3, FK3, RP4.
    eapply (sr_blk H HB); [exact KR2 | exact VIS2 | exact HF3 | exact RUN3 |].
    intros msF3 mo3 KR3 MP3 VIS3.
    pose proof (msteps_full asegs _ _ RUN3 HF3) as HF4. cbn [ms_regs] in HF4.
    rewrite <- (rfull_eq R4 HF4) in VIS3.
    apply K. exists R4, M3, s', LBi', b', cap', pid', errv'.
    split; [exact VIS3|]. split; [exact HF4|].
    split; [rewrite K43; change (getr R3 3) with (getr R1 3); exact T3|].
    split; [rewrite K44; change (getr R3 4) with (getr R1 4); exact T4|].
    assert (ZL : Zlen (ys ++ [xs_lit s]) = capi + 1) by (unfold Zlen in *; rewrite length_app; cbn [length]; lia).
    split.
    { unfold xg. rewrite ZL.
      exact (xrout_geo H s e bi capi ys b' (b' + 4 * cap') (b' + 4 * (capi + 1)) R4
               ltac:(destruct WF' as [X]; exact X) RP4). }
    split; [exact KR3|].
    split; [eapply (ah_mpres_trans H HB); [exact MP|]; eapply (ah_mpres_trans H HB); [exact MP1|];
            eapply (ah_mpres_trans H HB); [exact MP2 | exact MP3]|].

    destruct (xok0_hdr H HB e LBi' b' cap' pid' P GR') as [OKd OKds].
    assert (FF8 : x_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    pose proof (sh_lt_2_45 (x_ff e + 256) ltac:(lia)) as SB.
    assert (FKW : Forall (xok0 H e LBi') (fkw (xg e bi capi ys) (xs_fk s)) /\ Forall (xsl_ok H e) (fkw (xg e bi capi ys) (xs_fk s))
                  /\ disjoint_from (fkw (xg e bi capi ys) (xs_fk s)) (x_v e) 24
                  /\ disjoint_from (fkw (xg e bi capi ys) (xs_fk s)) b' (4 * Zlen (ys ++ [xs_lit s]))
                  /\ disjoint_from (fkw (xg e bi capi ys) (xs_fk s)) (sh b') (nsh (4 * cap'))
                  /\ disjoint_from (fkw (xg e bi capi ys) (xs_fk s)) (sh (x_v e)) 3
                  /\ Forall (fun iv : Z * Z => (b' <= fst iv /\ snd iv <= b' + 4 * cap') \/ (sh b' <= fst iv /\ snd iv <= sh b' + nsh (4 * cap'))
                              \/ (aceil <= fst iv /\ snd iv <= xSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (xXE H e) a))
                            (fkw (xg e bi capi ys) (xs_fk s))).
    { unfold fkw. cbn [g_ff xg]. destruct (Z.eqb_spec (xs_fk s) 0) as [K0|K0].
      - repeat (split; [first [apply Forall_nil | exact I]|]). apply Forall_nil.
      - assert (K5 : 5 <= xs_fk s) by (clear - WFK K0; lia). assert (K32 : xs_fk s < 32) by (clear - WFK K0; lia).
        destruct (xok0_shb H e LBi' (xs_fk s) P K5 K32) as [Y1 Y2].
        assert (B8' : b' mod 8 = 0) by (clear - B'16; Z.div_mod_to_equations; lia).
        assert (D1 : x_v e + 24 <= sh (x_ff e) \/ sh (x_ff e) + 32 <= x_v e).
        { destruct (pt_app_sh (x_v e) 24 (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left | right]; lia)) as [X|X];
            change (nsh 256) with 32 in X; lia. }
        assert (D2 : b' + 4 * cap' <= sh (x_ff e) \/ sh (x_ff e) + 32 <= b').
        { destruct (pt_app_sh b' (4 * cap') (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia)
                     ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in B'P; destruct B'P; [left|right]; lia)) as [X|X];
            change (nsh 256) with 32 in X; lia. }
        assert (D3 : sh b' + nsh (4 * cap') <= sh (x_ff e) \/ sh (x_ff e) + 32 <= sh b').
        { destruct (pt_sh_apart b' (4 * cap') (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) B8' FF8
                     ltac:(clear - B'F P3 P4; unfold AFS_SIZE, AFS_HDR in *; lia)) as [X|X]; change (nsh 256) with 32 in X; lia. }
        assert (D4 : sh (x_v e) + nsh 24 <= sh (x_ff e) \/ sh (x_ff e) + nsh 256 <= sh (x_v e)).
        { apply pt_sh_apart; [destruct VB; lia | lia | lia | lia | exact V8 | exact FF8 | clear - VF; lia]. }
        change (nsh 256) with 32 in D4. change (nsh 24) with 3 in D4.
        split; [apply Forall_cons; [exact Y1 | apply Forall_nil]|].
        split; [apply Forall_cons; [exact Y2 | apply Forall_nil]|].
        split; [clear - D1 K5 K32; cbn; split; [lia | exact I]|]. split; [clear - D2 ZL CP' K5 K32; cbn; split; [lia | exact I]|].
        split; [clear - D3 K5 K32; cbn; split; [lia | exact I]|]. split; [clear - D4 K5 K32; cbn; split; [lia | exact I]|].
        apply Forall_cons; [|apply Forall_nil]. right; right; right. intros a Ha. cbn [fst snd] in Ha. apply xXE_frm. right; left. clear - Ha WFK. lia. }
    destruct FKW as (FK1 & FK2 & FK3d & FK4 & FK5 & FK6 & FK7).
    split.
    { eapply (xframe_munch H HB e m2 M3 s' LBi' errv'); [exact P | exact PF2 | exact MU3 | exact WM3 | exact (MI3 MI2) | exact (SK3 _ _ ST2f) |].
      apply Forall_cons; [exact OKd | exact FK1]. }
    split.
    { cbn [xslotP]. eapply (xslot_keep H e (Some (xs_sv s)) m2 M3 _ SL2 MU3 WM3).
      apply Forall_cons; [exact OKds | exact FK2]. }
    split.
    { split.
      { eapply vec32A_set_endW; [exact VEC2 | destruct VB; unfold AIMG_TOP; lia | exact MU3 | exact FK3d | exact FK4 |]. rewrite ZL. exact CV3. }
      split.
      { intros _. rewrite ZL. eapply SHAD_transport; [exact SH2 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia. cbn [disjoint_from].
        split; [destruct (pt_app_sh (x_v e + 8) 8 b' (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left|right]; lia)); lia|].
        exact FK5. }
      split.
      { eapply addressable_transport; [exact AD2 | exact MU3 | exact WM3 |]. change (nsh 24) with 3. cbn [disjoint_from].
        split; [destruct (pt_app_sh (x_v e + 8) 8 (x_v e) 24 ltac:(destruct VB; lia) ltac:(lia) ltac:(destruct VB; lia)
                            ltac:(destruct VB; [left|right]; lia)) as [X|X]; change (nsh 24) with 3 in X; lia|].
        exact FK6. }
      split; [exact (wr_at_wmono _ _ _ _ WV2 WM3)|].
      split; [right; split; [lia | unfold LBi', v4_newLB; left; reflexivity]|].
      exact GR'. }
    split.
    { eapply (xpres_trans H); [exact XP1|]. eapply (xpres_trans H); [exact XP12|].
      eapply (xp_xstep H HB e LBi' b' cap' pid' s' m2 m2 M3 _ P GR' RH2 ltac:(lia) MU3 WM3).
      apply Forall_cons; [|exact FK7]. right; right; right. intros a Ha. cbn [fst snd] in Ha.
      unfold xXE. cbn [rin_ivs fst snd]. left. lia. }
    rewrite CFz, CMz in AL2. unfold cap', v4_newcap in *. clear - AL2 AL CS1 CS4. lia.
  Qed.

  Lemma xstep : forall s (e : xpent H) ys sv msF mo (Q : config -> Prop),
    xs_wf s -> site_runs s -> v4slow_stmt H (xs_c s) -> xpre H e -> XV e ->
    (xs_setslots s = true -> x_t e = xs_lit s) -> (xs_setslots s = false -> sv = Some (xs_sv s)) ->
    Zlen ys + 1 <= Zlen (x_xs e) + 3 ->
    xat H e (xs_pc s) (xs_rin s) ys sv (mkCfg msF mo) ->
    (forall cf', xat H e (xs_nx s) (fun g => xs_rout s g (g_e g)) (ys ++ [xs_lit s]) (Some (xs_sv s)) cf' -> as_SR H Q cf') ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros s e ys sv msF mo Q WF RUNS VS P XVH HT HSV YL AT K.
    pose proof (rt_bp_base H HH) as HB.
    destruct AT as (R & mL & sL & LBi & bi & capi & pidi & eL & VIS & HF & G3 & G4 & RP & KR & MP & PM).
    cbn [cfg_ms cfg_model] in VIS, MP.
    pose proof PM as (PF & _ & PV & _).
    pose proof PF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH & _).
    destruct (xvec_blk H HB e ys mL sL LBi bi capi pidi RH PV) as (LEN & _ & _).
    destruct (Z_lt_le_dec (Zlen ys) capi) as [LC|LC].
    - exact (xstep_fast H HH s e ys sv msF mo Q R mL sL LBi bi capi pidi eL WF RUNS P XVH HT HSV VIS HF G3 G4 RP KR MP PM LC K).
    - exact (xstep_slow s e ys sv msF mo Q R mL sL LBi bi capi pidi eL WF RUNS VS P XVH HT HSV YL VIS HF G3 G4 RP KR MP PM ltac:(lia) K).
  Qed.
End XPs2.

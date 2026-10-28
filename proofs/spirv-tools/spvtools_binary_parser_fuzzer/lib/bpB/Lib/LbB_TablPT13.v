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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_ContStmt LbB_ContV4 LbB_ContVot.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablOS LbB_TablPT1 LbB_TablPT2 LbB_TablPT4 LbB_TablPT5 LbB_TablPT6.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablPT7 LbB_TablPT8 LbB_TablPT9 LbB_TablPT10 LbB_TablPT11 LbB_TablPT12.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PT13.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Lemma pt_slow_branch : forall (e : ptent H) i msF mo (Q : config -> Prop) R mL sL LBi bi capi pidi eL,
    ppre H e -> 0 <= i < pn e -> Znth (pn e - 1 - i) (p_l e) <> 0 ->
    as_VIS H sL msF = MS R (p_F e) (Z_to_bv 64 PT_H2) (p_fc e) None mL (seg_rom asegs) -> rfull R ->
    getr R 3 = p_gp e -> getr R 4 = p_tp e -> PTH R (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i ->
    as_AKREL H sL (mkCfg msF mo) -> as_MPRES H (p_mo e) mo ->
    pmem H e (pys e i) 4 mL sL LBi bi capi pidi eL -> Zlen (pys e i) = capi ->
    (forall cf', pt_skip H e i cf' -> as_SR H Q cf') ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e i msF mo Q R mL sL LBi bi capi pidi eL P Hi T0 VIS HF G3 G4 RP KR MP PM LCeq K.
    pose proof (rt_bp_base H HH) as HB.
    destruct PM as (PF & PV & XP & AL).
    pose proof PF as (MI & AC & ST & _ & _ & _ & _ & SL0 & _ & _ & _ & _ & WL & _ & _ & RH & _).
    destruct (pt_span H e mL P MI AC XP) as (CS & SHP & PS0 & PS16).
    destruct (pt_elem H e mL i P Hi MI AC) as (CE & TR & k & SK & KC').
    set (ys := pys e i) in *. set (t := Znth (pn e - 1 - i) (p_l e)) in *.
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PS8 & _ & (PL & PH & P4 & _) & _).
    pose proof P as (_ & _ & _ & _ & _ & SPB & SPS & _ & _ & _ & RA & _ & _ & _ & _ & _ & _ & _ & _ & OBJ & _ & _ & RH0 & _ & _ & _ & _ & TRO & AL0 & _).
    pose proof (pgeo_of H e P) as G.
    destruct G as (SP16 & S45 & S132 & S1S & S1L & SPH & CEl & LO & F64 & FL & FH & _ & _ & _ & _ & _ & FS2 & _ & SHF1 & SHF2 & _ & FB & _
                   & V8 & VB & VL & VF & _ & _ & SV1 & SV2 & (N0 & N48) & TP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    destruct (pvec_blk H HB e ys mL sL LBi bi capi pidi RH PV) as (LEN & BK & DJV).
    pose proof PV as (_ & _ & _ & _ & _ & GR).
    destruct (pcap_bound H e LBi bi capi pidi P GR) as (CB1 & CB2 & CB3).
    pose proof (vgrow_ge capi ltac:(lia)) as VG.
    assert (VM : vgrow capi <= pcapm e).
    { unfold v4_newcap, pcapm, capmax, vgrow. pose proof (pys_len H e i ltac:(lia)) as YL. fold ys in YL. pose proof (Zlen_nonneg (p_xs e)) as XN. unfold pn in *. clear - YL XN LCeq CB1 CB3 Hi. lia. }
    assert (BR : 0 <= bi /\ bi + 4 * capi <= aceil).
    { destruct BK as [(C0 & B0)|(C0 & HIn & (A0 & _ & _ & _ & ACe & _))]; [subst; lia | lia]. }
    destruct (pslots_parts H e mL SL0 ltac:(lia)) as (_ & _ & C48).

    destruct (pt_r1a R (p_F e) (p_fc e) mL (seg_rom asegs) (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i (p_p e)
                t k RP ltac:(lia) ltac:(lia) N48 F64 ltac:(lia) ltac:(lia) WL PS0 PS16 PS8 CS SHP S45 S1S SPH C48 PL PH P4 CE TR SK KC')
      as (R1 & M1 & RUN1 & PX1 & L10 & KK1 & MU1 & WM1 & SK1 & MI1 & CL1).
    destruct (pt_ok0_local H e LBi P) as [OK0 OKS].
    assert (PF1 : pframe H e 4 M1 sL LBi eL).
    { eapply (pframe_munch H HB e 4 mL M1 sL LBi eL); [exact P | exact PF | exact MU1 | exact WM1 | exact (MI1 MI) | exact (SK1 _ _ ST)
        | apply Forall_cons; [exact OK0 | apply Forall_nil] | apply Forall_cons; [exact OKS | apply Forall_nil]]. }
    pose proof (pt_local_pvec H HB e ys mL M1 sL LBi bi capi pidi P RH PV MU1 WM1) as PV1.
    assert (XP1 : xpres H (p_LB e) (pSP e) (pXE H e) (p_m e) M1).
    { eapply (xpres_trans H); [exact XP|].
      eapply (xpres_of_munch H (p_s e) (p_LB e) (pSP e) (pXE H e) _ (p_m e) mL M1); [exact HB | exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [|apply Forall_nil]. right. intros a Ha. cbn [fst snd] in Ha.
      unfold pXE. cbn [rin_ivs]. right. apply rin_ivs_app. right. unfold pXS. cbn [rin_ivs fst snd]. lia. }
    clear PF PV XP MU1 WM1 SK1 MI1 OK0 OKS CS SHP SK KC' CE.

    destruct PV1 as (VEC1 & SH1 & AD1 & WV1 & OB1 & _).
    pose proof VEC1 as (_ & _ & _ & _ & _ & F0 & F8 & F16 & _).
    pose proof PF1 as (MI1 & AC1 & ST1 & S01 & ER1 & RA1 & _ & SL1 & _ & _ & _ & _ & _ & KC1 & RF1 & RH1 & OW1).
    destruct (pslots_parts H e M1 SL1 ltac:(lia)) as (C16 & C40 & C48b).
    assert (GZ : gz M1 (p_v e) 24) by (intros j Hj; eapply sh0_of_addressable; [exact AD1 | change (8 * (24 / 8)) with 24; lia]).
    destruct (pt_r1s R1 (p_F e) (p_fc e) M1 (seg_rom asegs) (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i t bi
                (bi + 4 * Zlen ys) (bi + 4 * capi) PX1 L10 ltac:(lia) S45 ltac:(lia) SPH ltac:(destruct VB; lia) ltac:(destruct VB; lia) V8
                C16 F0 F8 F16 GZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (R2 & RUN2 & PC2 & KK2 & L1 & L10b & L11).
    pose proof (CatSim.msteps_trans _ _ _ _ RUN1 RUN2) as RUN12.
    eapply (sr_blk H HB); [exact KR | exact VIS | exact HF | exact RUN12 |].
    intros msF1 mo1 KR1 MP1 VIS1.
    pose proof PC2 as (Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q26 & Q27).
    assert (T4 : getr R2 4 = p_tp e) by (rewrite (KK2 4%bv ltac:(inb)), (KK1 4%bv ltac:(inb)); exact G4).
    assert (T3 : getr R2 3 = p_gp e) by (rewrite (KK2 3%bv ltac:(inb)), (KK1 3%bv ltac:(inb)); exact G3).

    pose proof (pgrown_blocks H HB e LBi bi capi pidi P GR) as BL.
    assert (OBJ1 : obj_win H LBi (pLF e) (pS1 e) (p_lo e) (p_v e) 24).
    { pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                       & CX & B0C & BB & BD).
      eapply (pt_objwin_LBi H (p_LB e) LBi (p_LF e) (pLF e) (pSP e) (pS1 e) (p_lo e) (p_v e) (p_b e) (4 * p_cap e) OBJ);
        [ lia | destruct VL; [left | right]; lia
        | intros bb Hb; destruct (BL bb Hb) as [IN|(EQ & _)]; [left; exact IN | right; subst bb; cbn; split; reflexivity]
        | intros f Hf; right; exact Hf | destruct VB; lia | exact V8 | destruct BB; lia
        | destruct (Z.eq_dec (p_b e) 0) as [E|E]; [rewrite E; reflexivity | ]
        | lia | destruct BB; lia | destruct VB; [left | right]; lia
        | destruct (Z.eq_dec (p_b e) 0) as [E|E]; [right; pose proof (B0C E); lia | exact (BD E)]
        | destruct BB; [left | right]; lia | destruct VB; lia ].
      pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & _).
      destruct OLD as [(X & _)|(C0 & HIn0)]; [contradiction|].
      pose proof (ah_blocks H HB _ _ _ _ RH0 HIn0) as (_ & A16 & _). cbn [blk_addr fst snd] in A16.
      clear - A16; Z.div_mod_to_equations; lia. }
    assert (CLo : rw_cells asegs M1 (p_ff e + 32) [C4 (Z_to_bv 64 t)]) by exact CL1.
    destruct (pt_budget H HB e LBi bi capi pidi P GR ltac:(lia)) as (BU1 & BU2 & BU3).
    destruct (rt_bp_cost H HH) as [CFz CMz].
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & GC) & _).
    pose proof (closs_step_ICM capi ltac:(lia)) as CS1. pose proof (closs_mono capi (vgrow capi) (pcapm e) VM) as CS2.
    pose proof (closs_tele (p_cap e) capi (pcapm e)) as CS3. pose proof (closs_tele (p_cap e) capi (vgrow capi)) as CS4.
    assert (COST : as_Cm H (4 * v4_newcap capi) + as_Cf H (4 * capi) <= as_AL H sL).
    { rewrite CFz, CMz. unfold v4_newcap. clear - CS1 CS2 CS3 GC AL. lia. }
    eapply (ah_seq H HB).
    { eapply (v4slow_fe724 H HB) with (v := p_v e) (b := bi) (cap := capi) (src := p_ff e + 32) (x := t) (xs := ys) (pid := pidi)
        (LB := LBi) (LF := pLF e) (lo := p_lo e) (B := p_B e) (shi := p_shi e) (errv := eL);
      [ exact VIS1 | exact L10b | exact L11 | exact VEC1 | exact LCeq | exact V8 | exact AD1
      | rewrite Q2, u64_of_Z by lia; exact OBJ1
      | exact VB | exact WV1 | exact OW1 | exact OB1
      | intros Hc; pose proof (SH1 Hc) as X; rewrite LCeq in X; exact X
      | clear - CB2 VM; unfold v4_newcap; lia
      | rewrite Q2, u64_of_Z by lia; exact (pt_src_keep H e LBi (pS1 e) M1 t P CLo KC1 ltac:(lia))
      | change (v4_xmax VOT_SLOW_CREF) with (2 ^ 31); lia | clear - F64; Z.div_mod_to_equations; lia | lia | lia
      | exact RH1 | exact KR1
      | apply (rt_bp_live H HH sL LBi M1 (4 * v4_newcap capi) RH1); unfold v4_newcap; [lia | exact BU1 | exact BU2 | exact BU3]
      | exact COST
      | exact TRO | exact RA1 | rewrite Q2, u64_of_Z by lia; lia
      | rewrite Q2, u64_of_Z by lia; clear - S132; Z.div_mod_to_equations; lia
      | rewrite Q2, u64_of_Z by lia; lia
      | rewrite Q2, u64_of_Z by lia; exact (proj1 (stk_split asegs M1 (p_lo e) (pS1 e) (pSP e) ST1 ltac:(lia)))
      | exact CEl | rewrite Q2, u64_of_Z by lia; unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK; lia
      | rewrite T4; exact ER1 | exact MI1 | rewrite T4; exact TP
      | rewrite L1, u64_of_Z by (unfold PT_SL_RET; lia); reflexivity
      | exact AC1 | exact RF1 | exact S01 | rewrite Q2, u64_of_Z by lia; lia ]. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv' & s' & pid' & b' & POST).
    cbv zeta in POST.
    destruct POST as (VIS2 & KR2 & MP2 & MI2 & ST2 & ER2 & RA2 & XP2 & ABR2 & RH2 & VEC2 & SH2 & AD2 & WV2 & OW2 & RF2 & AC2 & S02 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite L1 in VIS2. rewrite (ret_pc_even PT_SL_RET ltac:(unfold PT_SL_RET; lia) eq_refl) in VIS2.
    rewrite Q2, u64_of_Z in ST2, XP2 by lia. rewrite T4 in ER2.
    set (cap' := v4_newcap capi) in *. set (LBi' := v4_newLB H LBi bi pidi pid' b' (4 * cap')) in *.
    assert (BK' : bi = 0 /\ capi = 0 \/ (0 < capi /\ ablock_range H bi (4 * capi))).
    { destruct BK as [(C0 & B0)|(C0 & HIn & ABR)]; [left; split; assumption | right; split; assumption]. }
    pose proof (pframe_v4 H e M1 m2 sL s' LBi LBi' bi capi eL errv' P PF1 BK' MI2 AC2 ST2 S02 ER2 RA2 RF2 RH2 OW2 XP2) as PF2.

    assert (CP' : capi + 1 <= cap') by (unfold cap', v4_newcap; lia).
    assert (CM' : cap' <= pcapm e) by (unfold cap', v4_newcap; exact VM).
    assert (GR' : pgrown H e LBi' b' cap' pid').
    { right. split; [lia|]. split; [|exact ABR2].
      unfold LBi'. exact (pt_newLB_eq H HB e LBi bi capi pidi pid' b' (4 * cap') P GR (ah_nodup H HB _ _ _ RH1)). }

    assert (XP12 : xpres H (p_LB e) (pSP e) (pXE H e) M1 m2).
    { destruct GR as [(E1 & E2 & E3 & E4)|(GG1 & GG2 & GG3)].
      - rewrite E2, E1, E3 in XP2.
        eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hb; exact Hb |].
        intros a Ha. unfold pXE. cbn [rin_ivs] in Ha |- *. destruct Ha as [Ha|Ha]; [left; exact Ha | right; apply rin_ivs_app; left; exact Ha].
      - destruct (pgrown_tail H HB e LBi bi capi pidi P GG2) as (LBt & EL & BLt).
        rewrite EL in XP2, RH1.
        assert (NI : ~ In pidi (map blk_id LBt)).
        { pose proof (ah_nodup H HB _ _ _ RH1) as NDi. cbn [map] in NDi. apply NoDup_cons_iff in NDi as [X _]. exact X. }
        assert (B0 : bi <> 0) by (pose proof GG3 as (A0 & _); lia).
        assert (XE : v4_oldx bi (4 * capi) = [(bi, bi + 4 * capi); (sh bi, sh bi + nsh (4 * capi))])
          by (unfold v4_oldx; destruct (Z.eqb_spec bi 0); [contradiction | reflexivity]).
        rewrite XE in XP2.
        change ((p_v e, p_v e + 24) :: [(bi, bi + 4 * capi); (sh bi, sh bi + nsh (4 * capi))])
          with ([(p_v e, p_v e + 24)] ++ [(bi, bi + 4 * capi); (sh bi, sh bi + nsh (4 * capi))]) in XP2.
        pose proof (pt_xp_drop H HB sL LBt pidi bi (4 * capi) (pS1 e) [(p_v e, p_v e + 24)] M1 M1 m2 RH1 NI ltac:(lia) XP2) as XP3.
        eapply (pt_xp_lift H LBt (pS1 e) [(p_v e, p_v e + 24)] (p_LB e) (pSP e) (pXE H e) M1 m2 XP3 ltac:(lia)).
        + intros bb Hb. destruct (BLt bb Hb) as [IN|(EQ & Cc & Bc)]; [left; exact IN|]. right. intros a Ha. subst bb.
          cbn [blk_addr blk_size fst snd] in Ha. apply pXE_old; assumption.
        + intros a Ha. cbn [rin_ivs] in Ha. destruct Ha as [Ha|[]]. unfold pXE. cbn [rin_ivs]. left. exact Ha. }
    clear XP2.

    pose proof PF2 as (_ & _ & ST2f & _ & _ & _ & _ & SL2 & _ & _ & _ & _ & _ & _ & _ & _ & _).
    destruct (pslots_parts H e m2 SL2 ltac:(lia)) as (_ & C40b & _).
    set (R3 := mkR (Z_to_bv 64 PT_SL_RET) (getr R2 2) (getr R2 3) (getr R2 4) t0' t1' t2' (getr R2 8) (getr R2 9)
                   (Z_to_bv 64 (b' + 4 * (capi + 1))) a1' a2' a3' a4' a5' a6' a7'
                   (getr R2 18) (getr R2 19) (getr R2 20) (getr R2 21) (getr R2 22) (getr R2 23) (getr R2 24) (getr R2 25)
                   (getr R2 26) (getr R2 27) t3' t4' t5' t6') in VIS2.
    assert (HF3 : rfull R3) by apply rfull_mkR.
    assert (PC3 : PTC R3 (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i) by exact PC2.
    assert (L10c : getr R3 10 = Z_to_bv 64 (b' + 4 * (capi + 1))) by reflexivity.
    pose proof ABR2 as (B'0 & B'16 & B'n & B'I & B'C & B'F & B'P).
    assert (B'g : 16 <= b') by (clear - B'0 B'16; Z.div_mod_to_equations; lia).
    destruct (pt_r2s R3 (p_F e) (p_fc e) m2 (seg_rom asegs) (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i (b' + 4 * (capi + 1))
                PC3 L10c ltac:(lia) ltac:(clear - B'16; Z.div_mod_to_equations; lia) S45 ltac:(lia) SPH PS0 PS16 ltac:(destruct VB; lia) ltac:(destruct VB; lia) V8 C40b
                ltac:(eapply sh0_of_addressable; [exact AD2 | change (8 * (24 / 8)) with 24; lia])
                ltac:(eapply vt_wr_sub; [exact WV2 | lia | lia | lia]) ltac:(clear - VL LO S1S; destruct VL; lia))
      as (R4 & M3 & RUN3 & PX4 & M8 & KK4 & MU3 & WM3 & SK3 & MI3 & CV3).
    eapply (sr_blk H HB); [exact KR2 | exact VIS2 | exact HF3 | exact RUN3 |].
    intros msF3 mo3 KR3 MP3 VIS3.
    pose proof (msteps_full asegs _ _ RUN3 HF3) as HF4. cbn [ms_regs] in HF4.
    rewrite <- (rfull_eq R4 HF4) in VIS3.
    apply K. exists R4, M3, s', LBi', b', cap', pid', errv'.
    split; [exact VIS3|]. split; [exact HF4|].
    split; [rewrite (KK4 3%bv ltac:(inb)); change (getr R3 3) with (getr R2 3); exact T3|].
    split; [rewrite (KK4 4%bv ltac:(inb)); change (getr R3 4) with (getr R2 4); exact T4|].
    split; [split; [exact PX4 | exact M8]|]. split; [exact KR3|].
    split; [eapply (ah_mpres_trans H HB); [exact MP|]; eapply (ah_mpres_trans H HB); [exact MP1|];
            eapply (ah_mpres_trans H HB); [exact MP2 | exact MP3]|].

    rewrite pys_step by lia. fold t. replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; exact T0). fold ys.
    assert (ZL : Zlen (ys ++ [t]) = capi + 1) by (unfold Zlen in *; rewrite length_app; cbn [length]; lia).
    destruct (pt_ok0_hdr H HB e LBi' b' cap' pid' P GR') as [OKd OKds].
    split.
    { eapply (pframe_munch H HB e 4 m2 M3 s' LBi' errv'); [exact P | exact PF2 | exact MU3 | exact WM3 | exact (MI3 MI2) | exact (SK3 _ _ ST2f)
        | apply Forall_cons; [exact OKd | apply Forall_nil] | apply Forall_cons; [exact OKds | apply Forall_nil]]. }
    split.
    { split.
      { eapply vec32A_set_end; [exact VEC2 | destruct VB; unfold AIMG_TOP; lia | exact MU3 |]. rewrite ZL. exact CV3. }
      split.
      { intros _. rewrite ZL. eapply SHAD_transport; [exact SH2 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia. cbn.
        split; [destruct (pt_app_sh (p_v e + 8) 8 b' (4 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left|right]; lia)); lia|].
        exact I. }
      split.
      { eapply addressable_transport; [exact AD2 | exact MU3 | exact WM3 |]. change (nsh 24) with 3. cbn.
        split; [destruct (pt_app_sh (p_v e + 8) 8 (p_v e) 24 ltac:(destruct VB; lia) ltac:(lia) ltac:(destruct VB; lia)
                            ltac:(destruct VB; [left|right]; lia)) as [X|X]; change (nsh 24) with 3 in X; lia|].
        exact I. }
      split; [exact (wr_at_wmono _ _ _ _ WV2 WM3)|].
      split; [right; split; [lia | unfold LBi', v4_newLB; left; reflexivity]|].
      exact GR'. }
    split.
    { eapply (xpres_trans H); [exact XP1|]. eapply (xpres_trans H); [exact XP12|].
      eapply (pt_xp_step H HB e LBi' b' cap' pid' s' m2 m2 M3 _ P GR' RH2 ltac:(lia) MU3 WM3).
      apply Forall_cons; [|apply Forall_nil]. right; right; right. intros a Ha. cbn [fst snd] in Ha.
      unfold pXE. cbn [rin_ivs fst snd]. left. lia. }
    rewrite CFz, CMz in AL2. unfold cap', v4_newcap in *. clear - AL2 AL CS1 CS4. lia.
  Qed.
End PT13.

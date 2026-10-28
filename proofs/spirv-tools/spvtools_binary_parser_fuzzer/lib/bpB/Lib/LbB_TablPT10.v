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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablPT7 LbB_TablPT8 LbB_TablPT9.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma pcap_bound {HCEIL : HeapCeil} : forall H (e : ptent H) LBi bi capi pidi, ppre H e -> pgrown H e LBi bi capi pidi ->
  capi <= pcapm e /\ 4 * pcapm e <= 2 ^ 26 /\ p_cap e <= capi.
Proof.
  intros H e LBi bi capi pidi P GR.
  pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (B1 & _) & _).
  assert (CM : p_cap e <= pcapm e) by (unfold pcapm, capmax; lia).
  destruct GR as [(E1 & _)|(G1 & _)]; [subst capi; split; [exact CM|]; split; [exact B1 | lia]|].
  split; [lia|]. split; [exact B1 | lia].
Qed.

Section PT10.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Lemma pt_fast_branch : forall (e : ptent H) i msF mo (Q : config -> Prop) R mL sL LBi bi capi pidi eL,
    ppre H e -> 0 <= i < pn e -> Znth (pn e - 1 - i) (p_l e) <> 0 ->
    as_VIS H sL msF = MS R (p_F e) (Z_to_bv 64 PT_H2) (p_fc e) None mL (seg_rom asegs) -> rfull R ->
    getr R 3 = p_gp e -> getr R 4 = p_tp e -> PTH R (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i ->
    as_AKREL H sL (mkCfg msF mo) -> as_MPRES H (p_mo e) mo ->
    pmem H e (pys e i) 4 mL sL LBi bi capi pidi eL -> Zlen (pys e i) < capi ->
    (forall cf', pt_skip H e i cf' -> as_SR H Q cf') ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e i msF mo Q R mL sL LBi bi capi pidi eL P Hi T0 VIS HF G3 G4 RP KR MP PM LC K.
    pose proof (rt_bp_base H HH) as HB.
    destruct PM as (PF & PV & XP & AL).
    pose proof PF as (MI & AC & ST & _ & _ & _ & _ & SL0 & _ & _ & _ & _ & WL & _ & _ & RH & _).
    destruct (pt_span H e mL P MI AC XP) as (CS & SHP & PS0 & PS16).
    destruct (pt_elem H e mL i P Hi MI AC) as (CE & TR & k & SK & KC').
    set (ys := pys e i) in *. set (t := Znth (pn e - 1 - i) (p_l e)) in *.
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PS8 & _ & (PL & PH & P4 & _) & _).
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CEl & LO & F64 & FL & FH & _ & _ & _ & _ & _ & FS2 & _ & SHF1 & SHF2 & _ & FB & _
                   & V8 & VB & VL & VF & _ & _ & SV1 & SV2 & (N0 & N48) & TP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    destruct (pvec_blk H HB e ys mL sL LBi bi capi pidi RH PV) as (LEN & BK & DJV).
    destruct BK as [(C0 & B0)|(C0 & HIn & ABR)]; [lia|].
    pose proof ABR as (A0 & A16 & An & AI & ACe & AF & AP).
    assert (B16 : 16 <= bi) by (clear - A0 A16; Z.div_mod_to_equations; lia).
    assert (B8 : bi mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
    pose proof PV as (_ & _ & _ & _ & _ & GR).
    destruct (pcap_bound H e LBi bi capi pidi P GR) as (CB1 & CB2 & CB3).
    assert (CB : 4 * capi <= 2 ^ 26) by (unfold vgrow in CB2; lia).
    specialize (DJV ltac:(lia)).
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
    { pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH0 & _).
      eapply (xpres_trans H); [exact XP|].
      eapply (xpres_of_munch H (p_s e) (p_LB e) (pSP e) (pXE H e) _ (p_m e) mL M1); [exact HB | exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [|apply Forall_nil]. right. intros a Ha. cbn [fst snd] in Ha.
      unfold pXE. cbn [rin_ivs]. right. apply rin_ivs_app. right. unfold pXS. cbn [rin_ivs fst snd]. lia. }
    clear PF PV XP MU1 WM1 SK1 MI1 OK0 OKS CS SHP SK KC' CE.

    destruct PV1 as (VEC1 & SH1 & AD1 & WV1 & OB1 & _).
    pose proof VEC1 as (_ & _ & _ & _ & _ & F0 & F8 & F16 & _).
    pose proof PF1 as (MI1 & AC1 & ST1 & _ & _ & _ & _ & SL1 & _ & _ & _ & _ & _ & _ & _ & RH1 & OW1).
    destruct (pslots_parts H e M1 SL1 ltac:(lia)) as (C16 & C40 & C48b).
    assert (GZ : gz M1 (p_v e) 24) by (intros j Hj; eapply sh0_of_addressable; [exact AD1 | change (8 * (24 / 8)) with 24; lia]).
    destruct (pt_r1f R1 (p_F e) (p_fc e) M1 (seg_rom asegs) (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i t bi
                (bi + 4 * Zlen ys) (bi + 4 * capi) PX1 L10 ltac:(lia) S45 ltac:(lia) SPH ltac:(destruct VB; lia) ltac:(destruct VB; lia) V8
                C16 F0 F8 F16 GZ B16 ltac:(lia) ltac:(lia) ltac:(lia))
      as (R2 & RUN2 & PC2 & KK2 & L1 & L10b & L11 & L12 & L13 & L24 & L25).
    pose proof (CatSim.msteps_trans _ _ _ _ RUN1 RUN2) as RUN12.
    eapply (sr_blk H HB); [exact KR | exact VIS | exact HF | exact RUN12 |].
    intros msF1 mo1 KR1 MP1 VIS1.
    pose proof PC2 as (Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q26 & Q27).

    eapply (ahh_evt_then H HB); [exact KR1 | exact VIS1 | |].
    { eapply (rt_bp_annot H HH) with (beg := bi) (len := 4 * capi) (oldmid := 4 * Zlen ys) (newmid := 4 * Zlen ys + 4) (lo := p_lo e);
        [ exact L10b | exact L11 | exact L12 | rewrite L13; f_equal; lia | exact B8 | lia | lia | lia | exact AP
        | unfold AAPP_HI; lia | exact (SH1 C0)
        | rewrite Q2, u64_of_Z by lia; exact (proj1 (stk_split asegs M1 (p_lo e) (pS1 e) (pSP e) ST1 ltac:(lia)))
        | exact CEl | rewrite Q2, u64_of_Z by lia; unfold AINTRIN_STACK; lia
        | exact MI1 | exact AC1
        | unfold in_app_mem; destruct (vt_band_of_aapp _ _ AP) as [X|X]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia ]. }
    intros msF2 mo2 KR2 MP2 POST.
    destruct POST as (u0 & u1 & u2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & u3 & u4 & u5 & u6 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & SH2 & AC2).
    rewrite L1 in VIS2. rewrite (ret_pc_even PT_AN_RET ltac:(unfold PT_AN_RET; lia) eq_refl) in VIS2.
    rewrite Q2, u64_of_Z in MU2, ST2 by lia. unfold AINTRIN_STACK in MU2.

    destruct (pt_ok0_sh H e LBi pidi bi capi P HIn ABR C0) as [OKa OKas].
    destruct (pt_ok0_stk H e LBi 4096 P ltac:(unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK; lia))
      as [OKb OKbs].
    assert (SHB : sh bi + nsh (4 * capi) <= sh (bi + 4 * capi) + 1) by (clear; unfold sh, nsh; Z.div_mod_to_equations; lia).
    pose proof (sh_lt_2_45 (bi + 4 * capi) ltac:(lia)) as SHB2.
    assert (ST2f : stk asegs m2 (p_lo e) (pSP e)).
    { apply (stk_merge asegs m2 (p_lo e) (pS1 e) (pSP e)); [exact ST2 | | lia].
      eapply stk_transport_disjoint; [exact (proj2 (stk_split asegs M1 (p_lo e) (pS1 e) (pSP e) ST1 ltac:(lia))) | exact MU2 | exact WM2 |].
      cbn. split; [lia|]. split; [lia | exact I]. }
    assert (PF2 : pframe H e 4 m2 sL LBi eL).
    { eapply (pframe_munch H HB e 4 M1 m2 sL LBi eL); [exact P | exact PF1 | exact MU2 | exact WM2 | exact MI2 | exact ST2f
        | apply Forall_cons; [exact OKa | apply Forall_cons; [exact OKb | apply Forall_nil]]
        | apply Forall_cons; [exact OKas | apply Forall_cons; [exact OKbs | apply Forall_nil]]]. }
    assert (DVS : sh (p_v e) + nsh 24 <= sh bi \/ sh bi + nsh (4 * capi) <= sh (p_v e)).
    { destruct (pt_sh_apart (p_v e) 24 bi (4 * capi) ltac:(destruct VB; lia) ltac:(lia) ltac:(lia) ltac:(lia) V8 B8 ltac:(lia)) as [X|X];
      [left | right]; lia. }
    change (nsh 24) with 3 in DVS.
    assert (CL2 : rw_cells asegs m2 (p_ff e + 32) [C4 (Z_to_bv 64 t)]).
    { eapply rw_cells_transport; [exact CL1 | exact MU2 | exact WM2 |]. cbn.
      split; [destruct (pt_app_sh (p_ff e + 32) 4 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct FB; [left|right]; lia)); lia|].
      split; [lia | exact I]. }
    assert (VEC2 : vec32A LBi m2 (p_v e) bi ys capi).
    { eapply (vec32A_munch LBi M1 m2 (p_v e) bi ys capi _ VEC1 MU2).
      - cbn. split; [destruct (pt_app_sh (p_v e) 24 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left|right]; lia)); lia|].
        split; [destruct VL; lia | exact I].
      - cbn. split; [destruct (pt_app_sh bi (4 * Zlen ys) bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia)
                                 ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)); lia|].
        split; [lia | exact I]. }
    assert (AD2 : addressable m2 (p_v e) 24).
    { eapply addressable_transport; [exact AD1 | exact MU2 | exact WM2 |]. change (nsh 24) with 3. cbn.
      split; [lia|]. split; [pose proof (sh_lt_2_45 (p_v e + 24) ltac:(destruct VB; lia)) as X;
                              assert (sh (p_v e) + 3 <= sh (p_v e + 24) + 1) by (clear; unfold sh; Z.div_mod_to_equations; lia); lia | exact I]. }
    assert (XP2 : xpres H (p_LB e) (pSP e) (pXE H e) (p_m e) m2).
    { eapply (xpres_trans H); [exact XP1|].
      eapply (pt_xp_step H HB e LBi bi capi pidi sL M1 M1 m2 _ P GR RH1 C0 MU2 WM2).
      apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; right; left. cbn [fst snd]. lia. }
    clear MU2 ST2 OKa OKas OKb OKbs.

    pose proof PF2 as (_ & _ & _ & _ & _ & _ & _ & SL2 & _ & _ & _ & _ & _ & _ & _ & RH2 & OW2).
    destruct (pslots_parts H e m2 SL2 ltac:(lia)) as (_ & C40b & _).
    destruct (vt_slot_shk m2 bi capi (Zlen ys) SH2 A16 ltac:(lia) ltac:(lia) LC) as (j & SJ & JC).
    assert (JC' : j = 0 \/ ((bi + 4 * Zlen ys) mod 8 = 0 /\ 4 <= j < 8)).
    { destruct JC as [J|J]; [left; exact J|]. right.
      assert (M4 : (bi + 4 * Zlen ys) mod 8 = 0 \/ (bi + 4 * Zlen ys) mod 8 = 4) by (clear - B8; Z.div_mod_to_equations; lia).
      lia. }
    assert (WE2 : wr_at asegs m2 (bi + 4 * Zlen ys) 4).
    { unfold lb_own in OW2. rewrite Forall_forall in OW2. pose proof (OW2 _ HIn) as W. cbn [blk_addr blk_size fst snd] in W.
      eapply vt_wr_sub; [exact W | lia | lia | lia]. }
    assert (WV2 : wr_at asegs m2 (p_v e + 8) 8).
    { eapply vt_wr_sub; [exact (wr_at_wmono _ _ _ _ WV1 WM2) | lia | lia | lia]. }
    assert (WV2' : wr_at asegs m2 (p_v e) 24) by exact (wr_at_wmono _ _ _ _ WV1 WM2).
    assert (DJS : bi + 4 * Zlen ys + 4 <= sh (p_v e + 8) \/ sh (p_v e + 8) + 1 <= bi + 4 * Zlen ys).
    { destruct (pt_app_sh (bi + 4 * Zlen ys) 4 (p_v e + 8) 8 ltac:(destruct VB; lia) ltac:(lia) ltac:(destruct VB; lia)
                 ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)) as [X|X];
      change (nsh 8) with 1 in X; lia. }
    set (R3 := mkR (Z_to_bv 64 PT_AN_RET) (getr R2 2) (getr R2 3) (getr R2 4) u0 u1 u2 (getr R2 8) (getr R2 9) d0 d1 d2 d3 d4 d5 d6 d7
                   (getr R2 18) (getr R2 19) (getr R2 20) (getr R2 21) (getr R2 22) (getr R2 23) (getr R2 24) (getr R2 25)
                   (getr R2 26) (getr R2 27) u3 u4 u5 u6) in VIS2.
    assert (HF3 : rfull R3) by apply rfull_mkR.
    assert (PC3 : PTC R3 (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i) by exact PC2.
    assert (L24' : getr R3 24 = Z_to_bv 64 (bi + 4 * Zlen ys + 4)) by exact L24.
    assert (L25' : getr R3 25 = Z_to_bv 64 (bi + 4 * Zlen ys)) by exact L25.
    destruct (pt_r2f R3 (p_F e) (p_fc e) m2 (seg_rom asegs) (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i t (bi + 4 * Zlen ys) j
                PC3 L24' L25' ltac:(lia) ltac:(lia) N48 F64 ltac:(lia) ltac:(lia) S45 ltac:(lia) SPH PS0 PS16
                ltac:(destruct VB; lia) ltac:(destruct VB; lia) V8 ltac:(lia) ltac:(lia) ltac:(clear - B8; Z.div_mod_to_equations; lia)
                C40b CL2 ltac:(lia) SJ JC' ltac:(eapply sh0_of_addressable; [exact AD2 | change (8 * (24 / 8)) with 24; lia])
                WE2 WV2 ltac:(lia) DJS ltac:(clear - VL LO S1S; destruct VL; lia) ltac:(left; clear - ACe CEl LO LC; lia))
      as (R4 & M3 & RUN3 & PX4 & M8 & KK4 & MU3 & WM3 & SK3 & MI3 & CL3 & CV3).
    eapply (sr_blk H HB); [exact KR2 | exact VIS2 | exact HF3 | exact RUN3 |].
    intros msF3 mo3 KR3 MP3 VIS3.
    pose proof (msteps_full asegs _ _ RUN3 HF3) as HF4. cbn [ms_regs] in HF4.
    rewrite <- (rfull_eq R4 HF4) in VIS3.
    apply K. exists R4, M3, sL, LBi, bi, capi, pidi, eL.
    split; [exact VIS3|]. split; [exact HF4|].
    split; [rewrite (KK4 3%bv ltac:(inb)); change (getr R3 3) with (getr R2 3); rewrite (KK2 3%bv ltac:(inb)), (KK1 3%bv ltac:(inb)); exact G3|].
    split; [rewrite (KK4 4%bv ltac:(inb)); change (getr R3 4) with (getr R2 4); rewrite (KK2 4%bv ltac:(inb)), (KK1 4%bv ltac:(inb)); exact G4|].
    split; [split; [exact PX4 | exact M8]|]. split; [exact KR3|].
    split; [eapply (ah_mpres_trans H HB); [exact MP|]; eapply (ah_mpres_trans H HB); [exact MP1|];
            eapply (ah_mpres_trans H HB); [exact MP2 | exact MP3]|].

    rewrite pys_step by lia. fold t. replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; exact T0). fold ys.
    destruct (pt_ok0_slot H e LBi pidi bi capi (bi + 4 * Zlen ys) P HIn ABR ltac:(lia) ltac:(lia)) as [OKc OKcs].
    destruct (pt_ok0_hdr H HB e LBi bi capi pidi P GR) as [OKd OKds].
    assert (ZL : 4 * Zlen (ys ++ [t]) = 4 * Zlen ys + 4) by (unfold Zlen; rewrite length_app; cbn [length]; lia).
    split.
    { eapply (pframe_munch H HB e 4 m2 M3 sL LBi eL); [exact P | exact PF2 | exact MU3 | exact WM3 | exact (MI3 MI2) | exact (SK3 _ _ ST2f)
        | apply Forall_cons; [exact OKc | apply Forall_cons; [exact OKd | apply Forall_nil]]
        | apply Forall_cons; [exact OKcs | apply Forall_cons; [exact OKds | apply Forall_nil]]]. }
    split.
    { split; [eapply (pt_vec_push LBi m2 M3 (p_v e) bi ys capi t VEC2 LC ltac:(lia) DJV ltac:(destruct VB; unfold AIMG_TOP; lia)
                                  MU3 CL3 CV3 ltac:(lia))|].
      split.
      { intros _. rewrite ZL. eapply SHAD_transport; [exact SH2 | exact MU3 | exact WM3 |].
        rewrite cc_gen_length by lia. cbn.
        split; [destruct (pt_app_sh (bi + 4 * Zlen ys) 4 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia)
                            ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)); lia|].
        split; [destruct (pt_app_sh (p_v e + 8) 8 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left|right]; lia)); lia|].
        exact I. }
      split.
      { eapply addressable_transport; [exact AD2 | exact MU3 | exact WM3 |]. change (nsh 24) with 3. cbn.
        split; [destruct (pt_app_sh (bi + 4 * Zlen ys) 4 (p_v e) 24 ltac:(destruct VB; lia) ltac:(lia) ltac:(destruct VB; lia)
                            ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)) as [X|X];
                change (nsh 24) with 3 in X; lia|].
        split; [destruct (pt_app_sh (p_v e + 8) 8 (p_v e) 24 ltac:(destruct VB; lia) ltac:(lia) ltac:(destruct VB; lia)
                            ltac:(destruct VB; [left|right]; lia)) as [X|X]; change (nsh 24) with 3 in X; lia|].
        exact I. }
      split; [exact (wr_at_wmono _ _ _ _ WV2' WM3)|].
      split; [exact OB1 | exact GR]. }
    split; [|exact AL].
    eapply (xpres_trans H); [exact XP2|].
    eapply (pt_xp_step H HB e LBi bi capi pidi sL m2 m2 M3 _ P GR RH2 C0 MU3 WM3).
    apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
    right; right; right. intros a Ha. cbn [fst snd] in Ha. unfold pXE. cbn [rin_ivs fst snd]. left. lia.
  Qed.
End PT10.

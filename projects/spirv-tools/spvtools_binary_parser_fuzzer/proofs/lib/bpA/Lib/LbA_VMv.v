(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0 AsWalk CXXRep RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_Own LbA_VecD1 LbA_VMvStmt
  LbA_VMv1 LbA_VMv2 LbA_VMv3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section VMv.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HANN : annotate_gen_stmt.
  Hypothesis HMSET : asan_memset_stmt.

  Definition vm_fin (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (v w b2 e2 c2 lo : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch W m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ ACONST m'
      /\ rw_cells asegs m' v [C8 (wz b2); C8 (wz e2); C8 (wz c2)] /\ rw_cells asegs m' w [C8 (wz 0); C8 (wz 0); C8 (wz 0)].

  Definition vm_pre1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (v w b1 c1 lo shi : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1,
      ms' = MS (mkR (Z_to_bv 64 AVMOVE_DEL_RA_1) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0' t1' t2' (Z_to_bv 64 v) (Z_to_bv 64 w)
                    (Z_to_bv 64 b1) (Z_to_bv 64 (c1 - b1)) a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (v + 16)) (Z_to_bv 64 (v + 8)) (Z_to_bv 64 0x7fff8000) (shw v) (shw (v + 16)) (shw (v + 8))
                    s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 AOPDEL2) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 80 - 4096, bv_unsigned sp); (v + 8, v + 16); (sh b1, sh b1 + nsh (c1 - b1))] m m1
      /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
      /\ SHAD m1 b1 (shadow_of (c1 - b1)) /\ ACONST m1 /\ stack0 m1 lo shi
      /\ rw_cells asegs m1 v [C8 (wz b1); C8 (wz b1); C8 (wz c1)]
      /\ rw_cells asegs m1 (bv_unsigned sp - 72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma vm_pre1_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (v w b1 e1 c1 lo shi : Z),
    a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 w ->
    rw_cells asegs m v [C8 (wz b1); C8 (wz e1); C8 (wz c1)] -> SHAD m v (repeat (b8 0) 3) -> v mod 8 = 0 ->
    aapp v 24 -> v + 24 <= bv_unsigned sp - AVMOVE_STACK ->
    b1 <> 0 -> aapp b1 (c1 - b1) -> b1 mod 16 = 0 -> b1 <= e1 <= c1 -> c1 - b1 <= 2 ^ 40 ->
    SHAD m b1 (cc_gen (c1 - b1) (e1 - b1)) -> (c1 <= v \/ v + 24 <= b1) ->
    stack0 m lo shi -> bv_unsigned sp <= shi ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AVMOVE_STACK ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (vm_pre1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v w b1 c1 lo shi m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVMOVE_1) fc None m (seg_rom asegs)).
  Proof.
    intros until shi. intros Ha0 Ha1 CV SV V8 VA VAP B0 BA B16 BE BL SB VBD S0 SHI ST CE LO SP16 SPR MI AC.
    eapply evt_cut; [eapply vm_a; eassumption|].
    intros ms2 (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m2 & EQ & MU & WM & MI2 & ST2 & CV2 & CF2
                & SV2 & S02 & SH2 & AC2).
    subst ms2.
    eapply evt_mono; [eapply vm_b; try eassumption; lia|].
    intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & EQ' & MU' & WM' & MI' & ST' & SH'
                & AC' & S0' & CV' & CF').
    exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact EQ'|].
    split.
    { eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU MU')].
      intros x Hx; cbn [app outside] in Hx |- *; clear - Hx; lia. }
    split; [exact (wmono_trans asegs _ _ _ WM WM')|].
    repeat (split; [assumption|]). assumption.
  Qed.

  Lemma vmove_1 : vmove_stmt_at H AVMOVE_1 AVMOVE_DEL_RA_1.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo
      s LB LF pid v w b1 e1 c1 b2 e2 c2 lo B shi errv.
    intros VIS Ha0 Ha1 CV VH CW WH VWD B0E B1P OWN RH KR CF RA SPB SP16 ST CE LO ERR MI TP AC RF S0 SHI TRC.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    assert (SPR : 2 ^ 45 <= spz <= 2 ^ 47) by (unfold AVMOVE_STACK, AFREE_STACK in LO; lia).
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK FR]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4). unfold AIMG_TOP in FS1. pose proof FS2 as FS2u. unfold AFS_SIZE in FS2u.
    destruct VH as (V8 & SV & fv & INV & FV1 & FV2).
    pose proof (FR fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
    pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
    assert (VA : aapp v 24) by (eapply aapp_sub; [exact FS4 | lia | unfold AFS_SIZE; lia]).
    assert (VLO : v + 24 <= lo) by lia.
    destruct WH as (W8 & SW & WPL).
    assert (WFACTS : (w + 24 <= lo \/ spz <= w) /\ aconst_ok (w, w + 24) /\ in_app_mem w (w + 24) /\ 0x6e6000 <= w
                     /\ w + 24 <= 2 ^ 47 /\ stack0_ok (w, w + 24) /\ afs_write_ok H LF (w, w + 24) /\ (forall LB0, aclient_write_ok H LB0 (w, w + 24))
                     /\ (w + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= w)).
    { destruct WPL as [(fw & INW & FW1 & FW2) | (WS1 & WS2)].
      - pose proof (FR fw INW) as (FKw & FWA1 & FWA2 & _ & _). pose proof (fsz_pos (ff_class fw) ltac:(lia)).
        assert (WA : aapp w 24) by (eapply aapp_sub; [exact FS4 | unfold AFS_HDR in FWA1; lia | lia]).
        pose proof (aapp_bounds w 24 WA ltac:(lia)) as (WB1 & WB2 & WB3 & WB4 & WB5). unfold AIMG_TOP in WB1.
        split; [left; lia|]. split; [eapply (aconst_ok_app w 24); [exact WA | cbn; lia | cbn; lia]|].
        split; [eapply aapp_in_app_mem; [exact WA | lia | lia]|]. split; [lia|]. split; [lia|].
        split; [eapply (stack0_ok_aapp w 24); [exact WA | cbn; lia | cbn; lia]|].
        split; [right; exists fw; split; [exact INW | cbn; lia]|].
        split; [intros LB0; right; right; right; right; left; cbn; unfold AFS_HDR, AFS_SIZE in *; lia|].
        unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in WA. lia.
      - unfold AVMOVE_STACK, AFREE_STACK in LO.
        split; [right; lia|].
        split; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity; cbn; lia | right; left; cbn; lia]|].
        split; [right; unfold AHI_LO, AAPP_HI, ASHADOW_BASE; lia|]. split; [lia|]. split; [lia|].
        split; [apply stack0_ok_app; cbn; unfold AHI_LO; lia|].
        split; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; split; lia|].
        split; [intros LB0; left; cbn; lia|]. right; lia. }
    destruct WFACTS as (WAP & WCO & WAM & WB1 & WB2 & WS0 & WFS & WCL & WBAND).
    assert (VDJ : sh v + 3 <= 0x10007fff8000 /\ (sh v + 3 <= v \/ v + 24 <= sh v) /\ (sh v + 3 <= w \/ w + 24 <= sh v)).
    { clear - VA WBAND WB1 WB2. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA. pose proof aceil_facts.
      unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }
    assert (WDJ : sh w + 3 <= 0x10007fff8000 /\ (sh w + 3 <= v \/ v + 24 <= sh w) /\ (sh w + 3 <= w \/ w + 24 <= sh w)).
    { clear - VA WBAND WB1 WB2. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA. pose proof aceil_facts.
      unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }

    assert (WHV : forall mm, as_RFS H LF mm -> stack0 mm lo shi -> shvis mm w (w + 24)).
    { intros mm RFm S0m. destruct WPL as [(fw & INW & FW1 & FW2) | (WS1 & WS2)].
      - pose proof (ah_frm_shvis H HH LF mm fw RFm INW) as HV.
        pose proof (FR fw INW) as (FKw & FWA1 & FWA2 & _ & _). pose proof (fsz_pos (ff_class fw) ltac:(lia)).
        unfold AFS_HDR in FWA1. eapply shvis_sub; [exact HV | lia | lia | lia | lia | lia].
      - unfold AVMOVE_STACK, AFREE_STACK in LO. eapply stack0_shvis; [exact S0m | lia | lia | lia]. }
    assert (VHV : forall mm, as_RFS H LF mm -> shvis mm v (v + 24)).
    { intros mm RFm. pose proof (ah_frm_shvis H HH LF mm fv RFm INV) as HV.
      eapply shvis_sub; [exact HV | lia | lia | lia | lia | lia]. }
    destruct (Z.eq_dec b1 0) as [Bz | Bnz].
    -
      destruct (B0E Bz) as [E1 C1]. subst b1 e1 c1.
      unfold AVMOVE_STACK, AFREE_STACK in LO.
      eapply (ahh_evt H HH (vm_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v w b2 e2 c2 lo
                [(spz - 80 - 4096, spz); (v, v + 24); (w, w + 24)] m)); [exact KR | exact VIS | |].
      { eapply evt_cut; [eapply vm_e; [exact Ha0 | exact Ha1 | exact CV | exact SV | exact VA | exact V8 | exact VLO | exact ST | exact CE
                                        | unfold AVMOVE_STACK, AFREE_STACK; lia | exact SP16 | exact SPR | exact MI | exact AC]|].
        intros ms1 (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ1 & MU1 & WM1 & MI1
                    & ST1 & AC1 & CV1 & CF1).
        subst ms1. fold spz in MU1, ST1, CF1.
        assert (CW1 : rw_cells asegs m1 w [C8 (wz b2); C8 (wz e2); C8 (wz c2)])
          by (eapply rw_cells_transport; [exact CW | exact MU1 | exact WM1 | cbn; destruct WAP; lia]).
        assert (SW1 : SHAD m1 w (repeat (b8 0) 3)).
        { eapply SHAD_transport; [exact SW | exact MU1 | exact WM1 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
          clear - WDJ SPR. lia. }
        assert (SV1 : SHAD m1 v (repeat (b8 0) 3)).
        { eapply SHAD_transport; [exact SV | exact MU1 | exact WM1 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
          clear - VDJ SPR. lia. }
        assert (RF1 : as_RFS H LF m1).
        { eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 |].
          apply Forall_cons; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; split; lia | apply Forall_nil]. }
        assert (S01 : stack0 m1 lo shi).
        { eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 |].
          apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO; lia | apply Forall_nil]. }
        eapply evt_mono.
        { eapply vm_copy; [exact HMSET | exact CV1 | exact SV1 | exact VA | exact V8 | exact VLO | exact CW1 | exact SW1 | exact (WHV m1 RF1 S01)
                          | exact W8 | exact WAM | exact WCO | exact WAP | exact VWD | exact WB1 | exact WB2 | exact CF1 | exact ST1 | exact CE
                          | unfold AVMOVE_STACK, AFREE_STACK; lia | exact SPR | exact MI1 | exact AC1]. }
        intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & EQ' & MU' & WM' & MI'
                    & ST' & AC' & CV' & CW').
        exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
        split; [rewrite Hsp; exact EQ'|].
        split.
        { eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU1 MU')]. intros x Hx; cbn [app outside] in Hx |- *; clear - Hx; lia. }
        split; [exact (wmono_trans asegs _ _ _ WM1 WM')|].
        split; [exact MI'|]. split; [exact ST'|]. split; [exact AC'|]. split; [exact CV' | exact CW']. }
      intros msF' mo' KR' MP' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & VIS' & MU' & WM'
                               & MI' & ST' & AC' & CV' & CW').
      assert (WV : Forall (fun iv : Z * Z => aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv)
                     [(spz - 80 - 4096, spz); (v, v + 24); (w, w + 24)]).
      { apply Forall_cons.
        { split; [left; cbn; lia|]. split; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; split; lia|].
          split; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity; cbn; lia | right; left; cbn; lia]|].
          apply stack0_ok_app; cbn; unfold AHI_LO; lia. }
        apply Forall_cons.
        { split; [right; right; right; right; left; cbn; unfold AFS_HDR, AFS_SIZE in *; lia|].
          split; [right; exists fv; split; [exact INV | cbn; lia]|].
          split; [eapply (aconst_ok_app v 24); [exact VA | cbn; lia | cbn; lia]|].
          eapply (stack0_ok_aapp v 24); [exact VA | cbn; lia | cbn; lia]. }
        apply Forall_cons; [split; [exact (WCL LB) | split; [exact WFS | split; [exact WCO | exact WS0]]] | apply Forall_nil]. }
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 K) WV) as WC.
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 (proj2 K)) WV) as WF.
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj2 (proj2 (proj2 K))) WV) as WS.
      exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', s.
      cbn [cfg_ms cfg_model].
      split; [exact VIS'|]. split; [exact KR'|]. split; [exact MP'|]. split; [exact MI'|]. split; [exact ST'|].
      split.
      { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
        eapply rw_cells_transport; [exact ERR | exact MU' | exact WM' | cbn; unfold ATP; lia]. }
      split; [eapply (ah_rauxv_frame H HH); [exact RA | exact MU' | exact WM' | exact WC]|].
      unfold vmove_LB, vmove_X. cbn [Z.eqb app].
      split.
      { eapply (xpres_of_munch H s LB spz _ _ m); [exact HH | exact RH | exact MU' | exact WM' |].
        apply Forall_cons; [left; cbn; lia|].
        apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia|].
        apply Forall_cons; [right; intros a Ha; cbn; right; left; cbn in Ha; lia | apply Forall_nil]. }
      split; [eapply (ah_RHEAP_frame H HH); [exact RH | exact MU' | exact WM' | exact WC]|].
      split; [exact (lb_own_wmono _ _ _ OWN WM')|].
      split; [exact CV'|]. split; [exact CW'|].
      split.
      { eapply SHAD_transport; [exact SV | exact MU' | exact WM' |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
        clear - VDJ SPR. lia. }
      split.
      { eapply SHAD_transport; [exact SW | exact MU' | exact WM' |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
        clear - WDJ SPR. lia. }
      split; [eapply (ah_RFS_frame H HH); [exact RF | exact MU' | exact WM' | exact WF]|].
      split; [exact AC'|].
      split; [eapply stack0_transport; [exact S0 | exact MU' | exact WM' | exact WS]|].
      pose proof (ah_costs H HH) as (_ & _ & CF0 & _). specialize (CF0 (0 - 0) ltac:(lia)). lia.
    -
      destruct (B1P Bnz) as (INB & BE & BL & SB & BDV & BDW).
      pose proof (ah_blocks H HH _ _ _ _ RH INB) as ABR. unfold blk_addr, blk_size in ABR. cbn [fst snd] in ABR.
      pose proof ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
      unfold AVMOVE_STACK, AFREE_STACK in LO.
      assert (SPH : sh b1 + nsh (c1 - b1) <= 0x10007fff8000)
        by (pose proof (sh_nsh_high b1 (c1 - b1) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
      assert (SHL : 0x7fff8000 <= sh b1) by (unfold sh, ASHADOW_BASE; pose proof (Z.div_pos b1 8 ltac:(lia) ltac:(lia)); lia).
      assert (BDJ : (sh v + 3 <= sh b1 \/ sh b1 + nsh (c1 - b1) <= sh v) /\ (sh w + 3 <= sh b1 \/ sh b1 + nsh (c1 - b1) <= sh w)).
      { clear - BDV BDW V8 W8 B16 BE. unfold sh, nsh. split; Z.div_mod_to_equations; nia. }

      eapply (ahh_evt_then H HH (vm_pre1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v w b1 c1 lo shi m)); [exact KR | exact VIS | |].
      { eapply vm_pre1_evt; try eassumption; unfold AVMOVE_STACK, AFREE_STACK in *; lia. }
      intros msF1 mo1 KR1 MP1 (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & VIS1 & MU1 & WM1 & MI1
                                & ST1 & SH1 & AC1 & S01 & CV1 & CF1).
      fold spz in VIS1, MU1, ST1, CF1.
      assert (W1 : Forall (fun iv : Z * Z => aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv)
                     [(spz - 80 - 4096, spz); (v + 8, v + 16); (sh b1, sh b1 + nsh (c1 - b1))]).
      { apply Forall_cons.
        { split; [left; cbn; lia|]. split; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; split; lia|].
          apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity; cbn; lia | right; left; cbn; lia]. }
        apply Forall_cons.
        { split; [right; right; right; right; left; cbn; unfold AFS_SIZE in *; lia|].
          split; [right; exists fv; split; [exact INV | cbn; lia]|].
          eapply (aconst_ok_app v 24); [exact VA | cbn; lia | cbn; lia]. }
        apply Forall_cons; [| apply Forall_nil].
        split; [right; right; right; left; exists (pid, b1, c1 - b1); split; [exact INB | cbn; lia]|].
        split.
        { left. cbn. pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE b1 (c1 - b1) FS4 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S.
          unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. split; lia. }
        apply aconst_ok_high; [cbn [fst snd]; apply sh_mono; unfold AIMG_TOP; lia | right; left; cbn; lia]. }
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv) => proj1 K) W1) as W1C.
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv) => proj1 (proj2 K)) W1) as W1F.
      assert (RH1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W1C]).
      assert (RA1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | exact W1C]).
      assert (RF1 : as_RFS H LF m1) by (eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 | exact W1F]).
      assert (ERR1 : rw_cells asegs m1 (errno_addr tp) [C4 errv]).
      { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
        eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; lia]. }
      pose proof (lb_own_wmono _ _ _ OWN WM1) as OWN1.
      destruct (rw_cells_of_own LB m1 (pid, b1, c1 - b1) OWN1 INB ltac:(cbn; unfold AIMG_TOP; lia) ltac:(cbn; lia)) as (bs & CB1).
      cbn [blk_addr blk_size fst snd] in CB1.

      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (LB := LB) (p := pid) (A := b1) (n := c1 - b1) (lo := lo) (B := B) (errv := errv) (CH := [])
                                     (sbs := shadow_of (c1 - b1)) (bs := bs);
          [exact VIS1 | exact RH1 | exact KR1 | exact INB | exact CF | exact CB1 | exact SH1 | rewrite shadow_of_length by lia; reflexivity
          | exact RA1 | rewrite u64_of_Z by lia; lia | rewrite u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo (spz - 80) spz ST1 ltac:(lia)))
          | exact CE | rewrite u64_of_Z by lia; unfold AFREE_STACK; lia | exact ERR1 | exact MI1 | exact TP
          | rewrite u64_of_Z by lia; clear - SP16; Z.div_mod_to_equations; lia | exact AC1
          | rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; lia
          | rewrite u64_of_Z by (unfold AVMOVE_DEL_RA_1; lia); exact (TRC Bnz) | reflexivity ]. }
      intros [msF2 mo2] POST2.
      destruct POST2 as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & sA
                         & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & RH2 & AC2 & AL2).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite u64_of_Z in ST2, AP2 by lia.
      rewrite (ret_pc_even AVMOVE_DEL_RA_1 ltac:(unfold AVMOVE_DEL_RA_1; lia) eq_refl) in VIS2.

      assert (CV2 : rw_cells asegs m2 v [C8 (wz b1); C8 (wz b1); C8 (wz c1)]).
      { eapply (apres_rw_cells H); [exact AP2 | exact CV1 |]. right; right; right; right; left. cbn. unfold AFS_SIZE in *. lia. }
      assert (CF2 : rw_cells asegs m2 (spz - 72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply (apres_rw_cells H); [exact AP2 | exact CF1 | left; lia]. }
      assert (CW2 : rw_cells asegs m2 w [C8 (wz b2); C8 (wz e2); C8 (wz c2)]).
      { assert (CW1 : rw_cells asegs m1 w [C8 (wz b2); C8 (wz e2); C8 (wz c2)])
          by (eapply rw_cells_transport; [exact CW | exact MU1 | exact WM1 | cbn; clear - WAP VWD WBAND SPH SHL LO CE SPR ACF1; lia]).
        eapply (apres_rw_cells H); [exact AP2 | exact CW1 |].
        destruct WPL as [(fw & INW & FW1 & FW2) | (WS1 & WS2)].
        - pose proof (FR fw INW) as (FKw & FWA1 & FWA2 & _ & _). pose proof (fsz_pos (ff_class fw) ltac:(lia)).
          right; right; right; right; left. cbn. unfold AFS_HDR, AFS_SIZE in *. lia.
        - left. cbn. lia. }
      assert (SVm1 : SHAD m1 v (repeat (b8 0) 3)).
      { eapply SHAD_transport; [exact SV | exact MU1 | exact WM1 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
        clear - VDJ BDJ SPR. lia. }
      assert (SV2 : SHAD m2 v (repeat (b8 0) 3)).
      { eapply (apres_SHAD H); [exact AP2 | exact SVm1 |]. right; right; right; right; right; left. cbn.
        clear - FA1 FV1 FV2 FA2 V8 FSZ. unfold sh, AFS_SIZE. Z.div_mod_to_equations. lia. }
      assert (SWm1 : SHAD m1 w (repeat (b8 0) 3)).
      { eapply SHAD_transport; [exact SW | exact MU1 | exact WM1 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
        clear - WDJ BDJ VWD SPR. lia. }
      assert (SW2 : SHAD m2 w (repeat (b8 0) 3)).
      { eapply (apres_SHAD H); [exact AP2 | exact SWm1 |].
        destruct WPL as [(fw & INW & FW1 & FW2) | (WS1 & WS2)].
        - pose proof (FR fw INW) as (FKw & FWA1 & FWA2 & _ & _). pose proof (fsz_pos (ff_class fw) ltac:(lia)) as FSZw.
          right; right; right; right; right; left. cbn.
          clear - FWA1 FW1 FW2 FWA2 W8 FSZw. unfold sh, AFS_HDR, AFS_SIZE in *. Z.div_mod_to_equations. lia.
        - right; right; right; right; right; right. cbn.
          assert (AW : aceil <= w) by lia. assert (WT : w + 24 <= 2 ^ 47) by lia.
          clear - AW WT W8. unfold sh, AHI_LO, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. }
      assert (FRM : forall a, 0 <= a < 2 ^ 64 -> (as_FSB H <= a < as_FSB H + AFS_SIZE \/ ATLS_PRIV_LO <= a < ATLS_PRIV_HI
                               \/ sh (as_FSB H) <= a < sh (as_FSB H + AFS_SIZE)) ->
                     m2 (wa a) = m1 (wa a) /\ (wview asegs m1 (wa a) <> None -> wview asegs m2 (wa a) <> None)).
      { intros a Ha Hr. apply (AP2 a Ha). unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
        - right; right; right; right; left; exact Hr.
        - right; left. unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. right; right; right; lia.
        - right; right; right; right; right; left; exact Hr. }
      assert (RF2 : as_RFS H LF m2) by (eapply (ah_RFS_ext H HH); [exact RF1 | exact FRM]).
      assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]).
      assert (ST2f : stk asegs m2 lo spz).
      { apply (stk_merge asegs m2 lo (spz - 80) spz); [exact ST2 | | lia].
        eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs m1 lo (spz - 80) spz ST1 ltac:(lia))) | lia]. }
      assert (OWN2 : lb_own (as_lb_remove H pid LB) m2).
      { pose proof (ah_lb_remove H HH) as (_ & _ & L3).
        eapply (lb_own_apres H); [exact (lb_own_incl LB _ m1 (L3 pid LB) OWN1) | exact AP2 | intros b Hb; exact Hb]. }

      eapply (ahh_evt H HH (vm_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v w b2 e2 c2 lo
                [(spz - 80 - 4096, spz); (v, v + 24); (w, w + 24)] m2)); [exact KR2 | exact VIS2 | |].
      { eapply evt_cut.
        { eapply vm_v0; [exact HMSET | exact (rw_cells_to_CB _ _ _ CV2) | exact SV2 | exact (VHV m2 RF2) | exact VA | exact V8 | exact VLO
                        | exact ST2f | exact CE | unfold AVMOVE_STACK, AFREE_STACK; lia | exact SPR | exact MI2 | exact AC2]. }
        intros ms3 (u0 & u1 & u2 & c0' & c1' & c2' & c3' & c4' & c5' & c6' & c7' & u3 & u4 & u5 & u6 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3
                    & AC3 & CV3).
        subst ms3.
        assert (CW3 : rw_cells asegs m3 w [C8 (wz b2); C8 (wz e2); C8 (wz c2)])
          by (eapply rw_cells_transport; [exact CW2 | exact MU3 | exact WM3 | cbn; clear - WAP VWD SPR LO CE ACF1; lia]).
        assert (CF3 : rw_cells asegs m3 (spz - 72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
          by (eapply rw_cells_transport; [exact CF2 | exact MU3 | exact WM3 | cbn; lia]).
        assert (SV3 : SHAD m3 v (repeat (b8 0) 3)).
        { eapply SHAD_transport; [exact SV2 | exact MU3 | exact WM3 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
          clear - VDJ SPR. lia. }
        assert (SW3 : SHAD m3 w (repeat (b8 0) 3)).
        { eapply SHAD_transport; [exact SW2 | exact MU3 | exact WM3 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
          clear - WDJ SPR. lia. }
        assert (RF3 : as_RFS H LF m3).
        { eapply (ah_RFS_frame H HH); [exact RF2 | exact MU3 | exact WM3 |].
          apply Forall_cons; [right; exists fv; split; [exact INV | cbn; lia]|].
          apply Forall_cons; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; split; lia | apply Forall_nil]. }
        assert (S03 : stack0 m3 lo shi).
        { eapply stack0_transport; [exact S02 | exact MU3 | exact WM3 |].
          apply Forall_cons; [eapply (stack0_ok_aapp v 24); [exact VA | cbn; lia | cbn; lia]|].
          apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO; lia | apply Forall_nil]. }
        eapply evt_mono.
        { eapply vm_copy; [exact HMSET | exact CV3 | exact SV3 | exact VA | exact V8 | exact VLO | exact CW3 | exact SW3 | exact (WHV m3 RF3 S03)
                          | exact W8 | exact WAM | exact WCO | exact WAP | exact VWD | exact WB1 | exact WB2 | exact CF3 | exact ST3 | exact CE
                          | unfold AVMOVE_STACK, AFREE_STACK; lia | exact SPR | exact MI3 | exact AC3]. }
        intros ms' (t0''' & t1''' & t2''' & a1''' & a2''' & a3''' & a4''' & a5''' & a6''' & a7''' & t3''' & t4''' & t5''' & t6''' & m' & EQ'
                    & MU' & WM' & MI' & ST' & AC' & CV' & CW').
        exists t0''', t1''', t2''', a1''', a2''', a3''', a4''', a5''', a6''', a7''', t3''', t4''', t5''', t6''', m'.
        split; [rewrite Hsp; exact EQ'|].
        split.
        { eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU3 MU')]. intros x Hx; cbn [app outside] in Hx |- *; clear - Hx; lia. }
        split; [exact (wmono_trans asegs _ _ _ WM3 WM')|].
        split; [exact MI'|]. split; [exact ST'|]. split; [exact AC'|]. split; [exact CV' | exact CW']. }
      intros msF' mo' KR' MP' (f0 & f1 & f2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & f3 & f4 & f5 & f6 & m' & VIS' & MU' & WM'
                               & MI' & ST' & AC' & CV' & CW').
      set (LB' := as_lb_remove H pid LB) in *.
      assert (WV : Forall (fun iv : Z * Z => aclient_write_ok H LB' iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv)
                     [(spz - 80 - 4096, spz); (v, v + 24); (w, w + 24)]).
      { apply Forall_cons.
        { split; [left; cbn; lia|]. split; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; split; lia|].
          split; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity; cbn; lia | right; left; cbn; lia]|].
          apply stack0_ok_app; cbn; unfold AHI_LO; lia. }
        apply Forall_cons.
        { split; [right; right; right; right; left; cbn; unfold AFS_HDR, AFS_SIZE in *; lia|].
          split; [right; exists fv; split; [exact INV | cbn; lia]|].
          split; [eapply (aconst_ok_app v 24); [exact VA | cbn; lia | cbn; lia]|].
          eapply (stack0_ok_aapp v 24); [exact VA | cbn; lia | cbn; lia]. }
        apply Forall_cons; [split; [exact (WCL LB') | split; [exact WFS | split; [exact WCO | exact WS0]]] | apply Forall_nil]. }
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB' iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 K) WV) as WC.
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB' iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 (proj2 K)) WV) as WF.
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB' iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj2 (proj2 (proj2 K))) WV) as WS.
      exists f0, f1, f2, g1, g2, g3, g4, g5, g6, g7, f3, f4, f5, f6, m', sA.
      cbn [cfg_ms cfg_model].
      split; [exact VIS'|]. split; [exact KR'|].
      split; [eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP']]|].
      split; [exact MI'|]. split; [exact ST'|].
      split.
      { eapply rw_cells_transport; [exact ERR2 | exact MU' | exact WM' |]. subst tp. rewrite u64_of_Z by (unfold ATP; lia).
        cbn. unfold ATP. clear - FA1 FV1 FS1 WB1 SPR. lia. }
      split; [eapply (ah_rauxv_frame H HH); [exact RA2 | exact MU' | exact WM' | exact WC]|].
      unfold vmove_LB, vmove_X. rewrite (proj2 (Z.eqb_neq b1 0) Bnz). fold LB'. cbn [app].
      split.
      { eapply xpres_trans.
        { eapply (xpres_of_munch H sA LB' spz _ _ m2 m m1); [exact HH | exact RH2 | exact MU1 | exact WM1 |].
          apply Forall_cons; [left; cbn; lia|].
          apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia|].
          apply Forall_cons; [right; intros a Ha; cbn; right; right; right; left; cbn in Ha; lia | apply Forall_nil]. }
        eapply xpres_trans.
        { eapply (xpres_weaken H LB' LB' (spz - 80) spz); [exact (xpres_of_apres H _ _ _ _ _ AP2) | lia | intros b Hb; exact Hb | intros a Ha; exact Ha]. }
        eapply (xpres_of_munch H sA LB' spz _ _ m2 m2 m'); [exact HH | exact RH2 | exact MU' | exact WM' |].
        apply Forall_cons; [left; cbn; lia|].
        apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia|].
        apply Forall_cons; [right; intros a Ha; cbn; right; left; cbn in Ha; lia | apply Forall_nil]. }
      split; [eapply (ah_RHEAP_frame H HH); [exact RH2 | exact MU' | exact WM' | exact WC]|].
      split; [exact (lb_own_wmono _ _ _ OWN2 WM')|].
      split; [exact CV'|]. split; [exact CW'|].
      split.
      { eapply SHAD_transport; [exact SV2 | exact MU' | exact WM' |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
        clear - VDJ SPR. lia. }
      split.
      { eapply SHAD_transport; [exact SW2 | exact MU' | exact WM' |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
        clear - WDJ SPR. lia. }
      split; [eapply (ah_RFS_frame H HH); [exact RF2 | exact MU' | exact WM' | exact WF]|].
      split; [exact AC'|].
      split; [eapply stack0_transport; [exact S02 | exact MU' | exact WM' | exact WS]|].
      exact AL2.
  Qed.
End VMv.

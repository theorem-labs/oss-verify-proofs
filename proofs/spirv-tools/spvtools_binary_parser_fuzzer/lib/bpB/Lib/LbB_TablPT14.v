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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablPT7 LbB_TablPT8 LbB_TablPT9 LbB_TablPT10 LbB_TablPT11 LbB_TablPT13.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PT14.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Lemma pt_head_step : forall (e : ptent H) i msF mo (Q : config -> Prop), ppre H e -> 0 <= i < pn e ->
    pt_head H e i (mkCfg msF mo) -> (forall cf', pt_skip H e i cf' -> as_SR H Q cf') -> as_SR H Q (mkCfg msF mo).
  Proof.
    intros e i msF mo Q P Hi HD K.
    pose proof (rt_bp_base H HH) as HB.
    destruct (Z.eq_dec (Znth (pn e - 1 - i) (p_l e)) 0) as [T0|T0].
    - exact (pt_step_skip H HB e i msF mo Q P Hi T0 HD K).
    - destruct HD as (R & mL & sL & LBi & bi & capi & pidi & eL & VIS & HF & G3 & G4 & RP & KR & MP & PM).
      cbn [cfg_ms cfg_model] in VIS, MP.
      pose proof PM as (_ & PV & _). pose proof PV as (VEC & _). pose proof VEC as (_ & _ & _ & LEN & _).
      destruct (Z_lt_le_dec (Zlen (pys e i)) capi) as [LC|LE].
      + exact (pt_fast_branch H HH e i msF mo Q R mL sL LBi bi capi pidi eL P Hi T0 VIS HF G3 G4 RP KR MP PM LC K).
      + exact (pt_slow_branch H HH e i msF mo Q R mL sL LBi bi capi pidi eL P Hi T0 VIS HF G3 G4 RP KR MP PM ltac:(lia) K).
  Qed.

  Lemma pframe_setk : forall e k k' mL M sL LBi eL,
    ppre H e -> pframe H e k mL sL LBi eL -> munch [(sh (p_ff e) + 4, sh (p_ff e) + 5)] mL M -> wmono asegs mL M ->
    mem_inv asegs M -> stk asegs M (p_lo e) (pSP e) -> rw_cells asegs M (sh (p_ff e) + 4) [C1 (b8 k')] ->
    pframe H e k' M sL LBi eL.
  Proof.
    intros e k k' mL M sL LBi eL P PF MU WM MI ST KC'.
    pose proof (rt_bp_base H HH) as HB.
    destruct PF as (MI0 & AC0 & ST0 & S00 & ER0 & RA0 & SV0 & SL0 & FP0 & WF0 & WS0 & WP0 & WL0 & KC0 & RF0 & RH0 & OW0).
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SHF0 & SHF1 & SHF2 & SHF3
                   & FB & PB & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP).
    pose proof P as (FF & _). pose proof (osframe_facts H _ _ _ FF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    set (W := [(sh (p_ff e) + 4, sh (p_ff e) + 5)]) in MU.
    assert (SHA : sh (as_FSB H) <= sh (p_ff e) /\ sh (p_ff e + 64) <= sh (as_FSB H + AFS_SIZE))
      by (split; apply sh_mono; unfold AFS_SIZE in *; lia).
    assert (W1 : Forall (aclient_write_ok H LBi) W).
    { apply Forall_cons; [|apply Forall_nil]. right; right; right; right; right; left. cbn [fst snd]. lia. }
    assert (W2 : Forall (afs_write_ok H (pLF e)) W).
    { apply Forall_cons; [|apply Forall_nil]. left. cbn [fst snd]. split; [unfold AFS_SIZE in *; lia | right; unfold ATLS_PRIV_HI, ATP; lia]. }
    assert (W3 : Forall aconst_ok W).
    { apply Forall_cons; [|apply Forall_nil].
      assert (sh AIMG_TOP <= sh (p_ff e)) by (apply sh_mono; unfold AIMG_TOP in *; lia).
      apply aconst_ok_high; [cbn [fst]; lia | right; left; cbn [fst]; unfold AIMG_TOP in *; replace (sh 7241728) with 0x800d5000 in * by reflexivity; lia]. }
    assert (W4 : Forall stack0_ok W).
    { apply Forall_cons; [|apply Forall_nil]. right. cbn [snd].
      assert (sh (p_ff e + 64) <= sh aceil) by (apply sh_mono; lia). lia. }
    destruct (client_frame H HB sL LBi (pLF e) (p_B e) W mL M RH0 RF0 AC0 RA0 MU WM W1 W2 W3) as (RH1 & RF1 & AC1 & RA1).
    assert (ERA : errno_addr (p_tp e) = ATP - 164) by (rewrite TP, HLib.u64_of_Z by (unfold ATP; lia); lia).
    pose proof (sh_lt_2_45 (p_ff e + 64) ltac:(lia)) as SB.
    unfold pframe.
    split; [exact MI|]. split; [exact AC1|]. split; [exact ST|].
    split; [eapply stack0_transport; [exact S00 | exact MU | exact WM | exact W4]|].
    split; [eapply rw_cells_transport; [exact ER0 | exact MU | exact WM |]; rewrite ERA; cbn; split; [unfold ATP; lia | exact I]|].
    split; [exact RA1|].
    split; [eapply rw_cells_transport; [exact SV0 | exact MU | exact WM |]; change (Z.of_nat (cells_size (psaved e))) with 104;
            cbn; split; [lia | exact I]|].
    split; [destruct SL0 as [SLa SLb]; split;
            [ eapply rw_cells_transport; [exact SLa | exact MU | exact WM |]; change (Z.of_nat (cells_size (pslots_lo e))) with 16;
              cbn; split; [lia | exact I]
            | intros NZ; eapply rw_cells_transport; [exact (SLb NZ) | exact MU | exact WM |]; change (Z.of_nat (cells_size (pslots e))) with 48;
              cbn; split; [lia | exact I] ]|].
    split; [eapply rw_cells_transport; [exact FP0 | exact MU | exact WM |]; cbn;
            split; [destruct FB; lia | exact I]|].
    split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WF0 WM)|]. split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WS0 WM)|].
    split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WP0 WM)|]. split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WL0 WM)|].
    split; [exact KC'|]. split; [exact RF1|]. split; [exact RH1|]. exact (lb_own_wmono _ _ _ OW0 WM).
  Qed.

  Lemma pt_skip_step : forall (e : ptent H) i msF mo (Q : config -> Prop), ppre H e -> 0 <= i < pn e ->
    pt_skip H e i (mkCfg msF mo) ->
    (i + 1 < pn e -> forall cf', pt_head H e (i + 1) cf' -> as_SR H Q cf') ->
    (i + 1 = pn e -> forall cf', pt_exit H e cf' -> as_SR H Q cf') ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e i msF mo Q P Hi SKP K1 K2.
    pose proof (rt_bp_base H HH) as HB.
    destruct SKP as (R & mL & sL & LBi & bi & capi & pidi & eL & VIS & HF & G3 & G4 & RP & KR & MP & PM).
    cbn [cfg_ms cfg_model] in VIS, MP.
    destruct PM as (PF & PV & XP & AL).
    pose proof PF as (MI & AC & ST & _ & _ & _ & _ & SL & _ & _ & WS & _ & _ & _ & _ & RH & _).
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SHF0 & SHF1 & SHF2 & SHF3
                   & FB & PB & V8 & VB & VL & VF & _ & _ & SV1 & SV2 & (N0 & N48) & TP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    destruct (pslots_parts H e mL SL ltac:(lia)) as (_ & _ & C48).
    destruct (pt_r2k R (p_F e) (p_fc e) mL (seg_rom asegs) (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i (proj1 RP) (proj2 RP)
                ltac:(lia) ltac:(lia) N48 F64 ltac:(lia) ltac:(lia) WS S45 S1S SPH C48)
      as (R1 & M1 & RUN & PX1 & L10 & L11 & KK & MU & WM & SK & MI1 & CL).
    pose proof (msteps_full asegs _ _ RUN HF) as HF1. cbn [ms_regs] in HF1.
    eapply (sr_blk H HB); [exact KR | exact VIS | exact HF | exact RUN |].
    intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.

    assert (PF1 : pframe H e (if i + 1 =? pn e then 0xf8 else 4) M1 sL LBi eL)
      by exact (pframe_setk e 4 _ mL M1 sL LBi eL P PF MU WM (MI1 MI) (SK _ _ ST) CL).
    destruct (pvec_blk H HB e (pys e (i + 1)) mL sL LBi bi capi pidi RH PV) as (LEN & BK & DJV).
    assert (PV1 : pvec H e (pys e (i + 1)) M1 LBi bi capi pidi).
    { eapply pvec_munch; [exact PV | exact MU | exact WM | | | |].
      - cbn. split; [|exact I]. destruct (pt_app_sh (p_v e) 24 (p_ff e) 64 ltac:(lia) ltac:(lia) ltac:(lia)
                                            ltac:(destruct VB; [left|right]; lia)) as [X|X]; change (nsh 64) with 8 in X; lia.
      - destruct BK as [(C0 & B0)|(C0 & HIn & (A0 & A16 & An & AI & ACe & AF & AP))]; [subst bi; cbn; split; [lia | exact I]|].
        cbn. split; [|exact I]. destruct (pt_app_sh bi (4 * Zlen (pys e (i + 1))) (p_ff e) 64 ltac:(lia) ltac:(lia) ltac:(lia)
                                   ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)) as [X|X];
          change (nsh 64) with 8 in X; lia.
      - intros Hc. destruct BK as [(C0 & B0)|(C0 & HIn & (A0 & A16 & An & AI & ACe & AF & AP))]; [lia|].
        assert (B8 : bi mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
        assert (F8 : p_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
        cbn. split; [|exact I].
        destruct (pt_sh_apart bi (4 * capi) (p_ff e) 64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) B8 F8
                   ltac:(unfold AFS_SIZE, AFS_HDR in *; lia)) as [X|X]; change (nsh 64) with 8 in X; lia.
      - assert (F8 : p_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
        cbn. split; [|exact I]. change (nsh 24) with 3.
        destruct (pt_sh_apart (p_v e) 24 (p_ff e) 64 ltac:(destruct VB; lia) ltac:(lia) ltac:(lia) ltac:(lia) V8 F8
                   ltac:(destruct VF; lia)) as [X|X]; change (nsh 64) with 8 in X; change (nsh 24) with 3 in X; lia. }
    assert (XP1 : xpres H (p_LB e) (pSP e) (pXE H e) (p_m e) M1).
    { pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH0 & _).
      eapply (xpres_trans H); [exact XP|].
      eapply (xpres_of_munch H (p_s e) (p_LB e) (pSP e) (pXE H e) _ (p_m e) mL M1); [exact HB | exact RH0 | exact MU | exact WM |].
      apply Forall_cons; [|apply Forall_nil]. right. intros a Ha. cbn [fst snd] in Ha.
      unfold pXE. cbn [rin_ivs]. right. apply rin_ivs_app. right. unfold pXS. cbn [rin_ivs fst snd]. lia. }
    destruct (Z.eqb_spec (i + 1) (pn e)) as [E|E].
    - apply (K2 E). exists 0xf8. exists R1, M1, sL, LBi, bi, capi, pidi, eL.
      split; [exact VIS1|]. split; [exact HF1|].
      split; [rewrite (KK 3%bv ltac:(inb)); exact G3|]. split; [rewrite (KK 4%bv ltac:(inb)); exact G4|].
      split; [destruct PX1 as (X2 & X8 & X9 & _ & _ & _ & _ & _ & _ & _ & X26 & _); split; [exact X8|]; split; [exact X9 | exact X26]|].
      split; [exact KR1|]. split; [exact (ah_mpres_trans H HB _ _ _ MP MP1)|].
      rewrite <- E. split; [exact PF1|]. split; [exact PV1|]. split; [exact XP1 | exact AL].
    - apply (K1 ltac:(lia)). exists R1, M1, sL, LBi, bi, capi, pidi, eL.
      split; [exact VIS1|]. split; [exact HF1|].
      split; [rewrite (KK 3%bv ltac:(inb)); exact G3|]. split; [rewrite (KK 4%bv ltac:(inb)); exact G4|].
      split; [split; [exact PX1 | split; [exact L10 | exact (L11 ltac:(lia))]]|].
      split; [exact KR1|]. split; [exact (ah_mpres_trans H HB _ _ _ MP MP1)|].
      split; [exact PF1|]. split; [exact PV1|]. split; [exact XP1 | exact AL].
  Qed.

  Lemma pt_loop : forall (e : ptent H) (Q : config -> Prop), ppre H e ->
    (forall cf, pt_exit H e cf -> as_SR H Q cf) ->
    forall (k : nat) i msF mo, Z.to_nat (pn e - i) = k -> 0 <= i < pn e -> pt_head H e i (mkCfg msF mo) -> as_SR H Q (mkCfg msF mo).
  Proof.
    intros e Q P KX k. induction k as [|k IH]; intros i msF mo Hk Hi HD; [lia|].
    eapply (pt_head_step e i msF mo Q P Hi HD).
    intros [msF' mo'] SKP.
    eapply (pt_skip_step e i msF' mo' Q P Hi SKP).
    - intros Hlt [msF'' mo''] HD'. eapply (IH (i + 1) msF'' mo''); [lia | lia | exact HD'].
    - intros _ cf' EX. exact (KX cf' EX).
  Qed.
End PT14.

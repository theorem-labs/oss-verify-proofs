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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_VecT LbA_VecD1 LbA_Own
  LbA_HKit LbA_HStKit LbA_StateStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section DtVDefs.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition dv_LB (LB : list block) (pid : bptr) (b : Z) : list block := if b =? 0 then LB else as_lb_remove H pid LB.
End DtVDefs.

Definition DV3 : Z := 0xeafc0.  Definition DV3_A1 : Z := 0xeb018.  Definition DV3_A2 : Z := 0xeb048.  Definition DV3_N : Z := 0xeb068.

Section DtV3.
  Context {HCEIL : HeapCeil}.
  Hypothesis HANN : annotate_gen_stmt.

  Definition dv3_mid1 (x24 x25 x26 x27 gp tp : word) (F : bvmap 5 word) (fc : bv 32) (st spf b c lo shi : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists w5 w6 w7 d10 d11 d12 d13 d14 d15 d16 d17 w28 w29 w30 w31 m2,
      ms' = MS (mkR (Z_to_bv 64 DV3_A1) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 216))
                    d10 d11 d12 d13 d14 d15 d16 d17 (Z_to_bv 64 (st + 232)) (Z_to_bv 64 (st + 224)) (Z_to_bv 64 0x7fff8000)
                    (shw (st + 216)) (shw (st + 232)) (shw (st + 224)) x24 x25 x26 x27 w28 w29 w30 w31)
               F (Z_to_bv 64 DV3_A1) fc None m2 (seg_rom asegs)
      /\ munch [(st + 224, st + 232); (sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)] m m2
      /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo spf
      /\ rw_cells asegs m2 (st + 216) [C8 (wz b); C8 (wz b); C8 (wz c)]
      /\ SHAD m2 (st + 216) (repeat (b8 0) 3) /\ stack0 m2 lo shi /\ SHAD m2 b (cc_gen (c - b) 0) /\ ACONST m2.

#[local] Definition HTbAHStDtV_0 : list (reg * expr) := [(8%bv, EVar 32); (2%bv, EVar 33); (20%bv, ELit 2147450880); (10%bv, EVar 32)].
  Lemma dv3_a : forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (st spf b e c lo shi : Z),
    rw_cells asegs m (st + 216) [C8 (wz b); C8 (wz e); C8 (wz c)] -> SHAD m (st + 216) (repeat (b8 0) 3) -> st mod 8 = 0 ->
    aapp st ST_SIZE ->
    b <> 0 -> aapp b (c - b) -> b mod 16 = 0 -> b <= e <= c -> c - b <= 2 ^ 40 ->
    SHAD m b (cc_gen (c - b) (e - b)) -> (c <= st + 216 \/ st + 240 <= b) ->
    stack0 m lo shi -> spf <= shi ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (dv3_mid1 x24 x25 x26 x27 gp tp F fc st spf b c lo shi m)
      (MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 (Z_to_bv 64 st) x11 x12 x13 x14 x15 x16 x17 x18 x19
               (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 DV3) fc None m (seg_rom asegs)).
  Proof.
    intros until shi. intros CV SV V8 VA0 B0 BA B16 BE BL SB VBD S0 SHI ST CE LO SP16 SPR MI AC.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VA : aapp (st + 216) 24) by (eapply aapp_sub; [exact VA0 | lia | unfold ST_SIZE; lia]).
    pose proof (aapp_bounds st ST_SIZE VA0 ltac:(unfold ST_SIZE; lia)) as (SB1' & SB2' & SB3' & SB4' & SB5').
    unfold AFREE_STACK, ST_SIZE, AIMG_TOP in *.
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (aapp_bounds (st + 216) 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5).
    pose proof (aapp_bounds b (c - b) BA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
    unfold AIMG_TOP in VB1, PB1.
    remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 (Z_to_bv 64 st) x11 x12 x13 x14 x15 x16 x17 x18 x19
               (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 b; Z_to_bv 64 e; Z_to_bv 64 c]).
    assert (HR : regs_ok E (srs sr_id HTbAHStDtV_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (GZV : gz m (st + 216) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
    assert (HK : know_ok asegs E m
       (kn_fix 20 [AANNOTATE_CC] (SCR [] [] []) DV3 (srs sr_id HTbAHStDtV_0)
       [ KWord (SA (EVar 32) 216) 8 (EVar 34); KWord (SA (EVar 32) 224) 8 (EVar 35); KWord (SA (EVar 32) 232) 8 (EVar 36);
         KWr (SA (EVar 32) 216) (ELit 24);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47); KRange (EVar 34) 0x6e6000 (2 ^ 47) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV 8%nat (C8 (wz e)). }
      apply Forall_cons. { kword_cell CV 16%nat (C8 (wz c)). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact (proj2 CV) | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R DV3 m (seg_rom asegs) HR HK 200%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 SB0 SB1' SB2'.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: first [ sc_shdj | sc_dj ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rreg HR' 12%bv L12. rreg HR' 13%bv L13. rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23.
    rewrite ?w_add in L9, L18, L19, L21, L22, L23 by lia.

    assert (WV1 : forall a, st + 216 <= a -> a + 8 <= st + 240 -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (proj2 CV) as W. destruct W as (W1 & W2 & W). cbn [cells_size csize Z.of_nat] in W.
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (st + 216 + (a - (st + 216) + i)) by lia. apply W. cbn. lia. }
    assert (MU1 : munch [(st + 224, st + 232)] m M1).
    { subst M1. clear - Hlf VB1 VB2 VB3 SPR LO CE ACF1 ACF2. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spf) by (subst M1; apply stk_mem_denot; exact ST).
    assert (SVP : sh b + nsh (c - b) <= st + 216 \/ st + 240 <= sh b)
      by (pose proof (aapp_disjoint_sh (st + 216) 24 b (c - b) VA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)); lia).
    assert (SPH : sh b + nsh (c - b) <= 0x10007fff8000)
      by (pose proof (sh_nsh_high b (c - b) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
    assert (SPA : sh b + nsh (c - b) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHV : sh (st + 216) + 3 <= sh b \/ sh b + nsh (c - b) <= sh (st + 216)).
    { clear - VBD V8 B16 BE. unfold sh, nsh. Z.div_mod_to_equations. nia. }
    assert (SB1 : SHAD M1 b (cc_gen (c - b) (e - b))).
    { eapply SHAD_transport; [exact SB | exact MU1 | exact WM1 |]. rewrite cc_gen_length by lia. cbn. lia. }
    assert (SV1 : SHAD M1 (st + 216) (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV | exact MU1 | exact WM1 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      unfold sh, ASHADOW_BASE. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA. Z.div_mod_to_equations. lia. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [eapply (stack0_ok_aapp (st + 216) 24); [exact VA | cbn; lia | cbn; lia] | apply Forall_nil]. }
    assert (AC1 : ACONST M1).
    { eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |].
      apply Forall_cons; [eapply (aconst_ok_app (st + 216) 24); [exact VA | cbn; lia | cbn; lia] | apply Forall_nil]. }
    assert (CV1 : rw_cells asegs M1 (st + 216) [C8 (wz b); C8 (wz b); C8 (wz c)]).
    { change [C8 (wz b); C8 (wz e); C8 (wz c)] with ([C8 (wz b)] ++ [C8 (wz e)] ++ [C8 (wz c)]) in CV.
      apply rw_cells_app in CV as [CV0 CV']. apply rw_cells_app in CV' as [_ CV2].
      replace (st + 216 + Z.of_nat (cells_size [C8 (wz b)]) + Z.of_nat (cells_size [C8 (wz e)])) with (st + 232) in CV2 by (cbn; lia).
      apply rw_cells_cons8_c.
      { eapply rw_cells_transport; [exact CV0 | exact MU1 | exact WM1 | cbn; lia]. }
      apply rw_cells_cons8_c.
      { subst M1. clear - Hlf WV1 VB1 VB2 VB3 SPR LO CE ACF1 ACF2. replace (st + 216 + 8) with (st + 224) by lia.
        lgcell Hlf (WV1 (st + 224) ltac:(lia) ltac:(lia)) 0%nat. }
      replace (st + 216 + 8 + 8) with (st + 232) by lia.
      eapply rw_cells_transport; [exact CV2 | exact MU1 | exact WM1 | cbn; lia]. }

    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L8, L9, L10, L11, L12, L13, L18, L19, L20, L21, L22, L23.
    clear HRe HR' Hlf Hms HF1 L1 L2 L8 L9 L10 L11 L12 L13 L18 L19 L20 L21 L22 L23.
    eapply evt_cut.
    { eapply HANN with (beg := b) (len := c - b) (oldmid := e - b) (newmid := 0) (lo := lo); rewrite ?u64_of_Z by lia.
      - reflexivity.
      - f_equal; lia.
      - f_equal; lia.
      - rewrite Z.add_0_r. reflexivity.
      - Z.div_mod_to_equations; lia.
      - lia.
      - lia.
      - lia.
      - exact BA.
      - unfold AAPP_HI; lia.
      - exact SB1.
      - exact ST1.
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact MI1.
      - exact AC1.
      - eapply aapp_in_app_mem; [exact BA | lia | lia]. }
    intros ms2 POST2.
    destruct POST2 as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m2 & EQ2 & MU2 & WM2 & MI2 & ST2 & SH2 & AC2).
    subst ms2. rewrite u64_of_Z in MU2, ST2 by lia.
    rewrite (ret_pc_even 962584 ltac:(lia) eq_refl).
    assert (CV2 : rw_cells asegs m2 (st + 216) [C8 (wz b); C8 (wz b); C8 (wz c)])
      by (eapply rw_cells_transport; [exact CV1 | exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; lia]).
    assert (SV2 : SHAD m2 (st + 216) (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV1 | exact MU2 | exact WM2 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      assert (sh (st + 216) + 3 <= 0x10007fff8000) by (unfold sh, ASHADOW_BASE; unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA; Z.div_mod_to_equations; lia).
      unfold AINTRIN_STACK. lia. }
    assert (S02 : stack0 m2 lo shi).
    { eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 |].
      apply Forall_cons; [right; cbn; exact SPA|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO, AINTRIN_STACK; lia | apply Forall_nil]. }
    apply evt_done. exists w0, w1, w2, d0, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m2.
    split; [reflexivity|].
    split; [exact (munch_app _ _ _ _ _ MU1 MU2)|].
    split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact CV2|].
    split; [exact SV2|]. split; [exact S02|]. split; [exact SH2 | exact AC2].
  Qed.
End DtV3.

Section DtV3b.
  Context {HCEIL : HeapCeil}.
  Hypothesis HANN : annotate_gen_stmt.

  Definition dv3_del (x24 x25 x26 x27 gp tp : word) (F : bvmap 5 word) (fc : bv 32) (st spf b c lo shi : Z) (m2 : mem)
      : machine_state -> Prop :=
    fun ms' => exists w5 w6 w7 a2' a3' a4' a5' a6' a7' w28 w29 w30 w31 m',
      ms' = MS (mkR (Z_to_bv 64 DV3_N) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 216))
                    (Z_to_bv 64 b) (Z_to_bv 64 (c - b)) a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (st + 232)) (Z_to_bv 64 (st + 224)) (Z_to_bv 64 0x7fff8000)
                    (shw (st + 216)) (shw (st + 232)) (shw (st + 224)) x24 x25 x26 x27 w28 w29 w30 w31)
               F (Z_to_bv 64 AOPDEL2) fc None m' (seg_rom asegs)
      /\ munch [(sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)] m2 m'
      /\ wmono asegs m2 m' /\ mem_inv asegs m' /\ stk asegs m' lo spf
      /\ SHAD m' b (shadow_of (c - b)) /\ ACONST m' /\ stack0 m' lo shi
      /\ rw_cells asegs m' (st + 216) [C8 (wz b); C8 (wz b); C8 (wz c)].

#[local] Definition HTbAHStDtV_1 : list (reg * expr) := [(2%bv, EVar 33); (8%bv, EVar 32); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 216)); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 232)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 224)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880))].
  Lemma dv3_b : forall (w5 w6 w7 d10 d11 d12 d13 d14 d15 d16 d17 x24 x25 x26 x27 w28 w29 w30 w31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (m2 : mem) (st spf b c lo shi : Z),
    stk asegs m2 lo spf -> mem_inv asegs m2 ->
    rw_cells asegs m2 (st + 216) [C8 (wz b); C8 (wz b); C8 (wz c)] ->
    SHAD m2 (st + 216) (repeat (b8 0) 3) -> stack0 m2 lo shi -> SHAD m2 b (cc_gen (c - b) 0) -> ACONST m2 ->
    st mod 8 = 0 -> aapp st ST_SIZE ->
    b <> 0 -> aapp b (c - b) -> b mod 16 = 0 -> b <= c -> c - b <= 2 ^ 40 -> (c <= st + 216 \/ st + 240 <= b) ->
    spf <= shi ->
    aceil <= lo -> lo <= spf - AFREE_STACK -> spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 ->
    evt asegs (dv3_del x24 x25 x26 x27 gp tp F fc st spf b c lo shi m2)
      (MS (mkR (Z_to_bv 64 DV3_A1) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 216))
               d10 d11 d12 d13 d14 d15 d16 d17 (Z_to_bv 64 (st + 232)) (Z_to_bv 64 (st + 224)) (Z_to_bv 64 0x7fff8000)
               (shw (st + 216)) (shw (st + 232)) (shw (st + 224)) x24 x25 x26 x27 w28 w29 w30 w31)
          F (Z_to_bv 64 DV3_A1) fc None m2 (seg_rom asegs)).
  Proof.
    intros until shi. intros ST2 MI2 CV2 SV2 S02 SH2 AC2 V8 VA0 B0 BA B16 BE BL VBD SHI CE LO SP16 SPR.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VA : aapp (st + 216) 24) by (eapply aapp_sub; [exact VA0 | lia | unfold ST_SIZE; lia]).
    pose proof (aapp_bounds st ST_SIZE VA0 ltac:(unfold ST_SIZE; lia)) as (SB1' & SB2' & SB3' & SB4' & SB5').
    unfold AFREE_STACK, ST_SIZE, AIMG_TOP in *.
    pose proof (stack0_bounds m2 lo shi S02) as SB0. unfold AAPP_HI in SB0.
    pose proof (aapp_bounds (st + 216) 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5).
    pose proof (aapp_bounds b (c - b) BA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
    unfold AIMG_TOP in VB1, PB1.
    assert (SVP : sh b + nsh (c - b) <= st + 216 \/ st + 240 <= sh b)
      by (pose proof (aapp_disjoint_sh (st + 216) 24 b (c - b) VA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)); lia).
    assert (SPH : sh b + nsh (c - b) <= 0x10007fff8000)
      by (pose proof (sh_nsh_high b (c - b) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
    assert (SPA : sh b + nsh (c - b) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).

    lazymatch goal with |- evt _ _ (MS ?T _ _ _ _ _ _) => remember T as R2 eqn:HR2 end.
    pose (E2 := Eseed R2 [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 b; Z_to_bv 64 c]).
    assert (HR2s : regs_ok E2 (srs sr_id HTbAHStDtV_1) R2).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R2; evs; try reflexivity;
        unfold shw; rewrite ?w_addm, ?w_add by lia; reflexivity. }
    assert (GZV2 : gz m2 (st + 216) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV2 | cbn; lia]).
    assert (HK2 : know_ok asegs E2 m2
       (kn_fix 20 [AANNOTATE_CC] (SCR [] [] []) DV3_A1
          (srs sr_id HTbAHStDtV_1)
       [ KWord (SA (EVar 32) 216) 8 (EVar 34); KWord (SA (EVar 32) 224) 8 (EVar 34); KWord (SA (EVar 32) 232) 8 (EVar 35);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47); KRange (EVar 34) 0x6e6000 (2 ^ 47) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CV2 0%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV2 8%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV2 16%nat (C8 (wz c)). }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R2 DV3_A1 m2 (seg_rom asegs) HR2s HK2 200%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E2 VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 SB0 SB1' SB2'.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: first [ sc_shdj | sc_dj ]. }
    clear HK2.
    assert (HF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF2) as HF2'. cbn [ms_regs] in HF2'.
    readback HR' HF2' HR2 HRe2.
    rreg HR' 1%bv K1. rreg HR' 10%bv K10. rreg HR' 11%bv K11. rreg HR' 12%bv K12. rreg HR' 13%bv K13.
    rreg HR' 2%bv K2. rreg HR' 8%bv K8. rreg HR' 9%bv K9. rreg HR' 18%bv K18. rreg HR' 19%bv K19. rreg HR' 20%bv K20.
    rreg HR' 21%bv K21. rreg HR' 22%bv K22. rreg HR' 23%bv K23.
    rewrite ?w_add in K9, K18, K19, K21, K22, K23 by lia.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe2, K1, K10, K11, K12, K13, K2, K8, K9, K18, K19, K20, K21, K22, K23.
    clear HRe2 HR' Hlf Hms HF2' K1 K10 K11 K12 K13 K2 K8 K9 K18 K19 K20 K21 K22 K23.

    eapply evt_cut.
    { eapply HANN with (beg := b) (len := c - b) (oldmid := 0) (newmid := c - b) (lo := lo); rewrite ?u64_of_Z by lia.
      - reflexivity.
      - f_equal; lia.
      - rewrite Z.add_0_r. reflexivity.
      - f_equal; lia.
      - Z.div_mod_to_equations; lia.
      - lia.
      - lia.
      - lia.
      - exact BA.
      - unfold AAPP_HI; lia.
      - exact SH2.
      - exact ST2.
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact MI2.
      - exact AC2.
      - eapply aapp_in_app_mem; [exact BA | lia | lia]. }
    intros ms4 POST4.
    destruct POST4 as (v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m4 & EQ4 & MU4 & WM4 & MI4 & ST4 & SH4 & AC4).
    subst ms4. rewrite u64_of_Z in MU4, ST4 by lia.
    rewrite (ret_pc_even 962632 ltac:(lia) eq_refl).
    rewrite cc_gen_full in SH4.

    assert (CV4 : rw_cells asegs m4 (st + 216) [C8 (wz b); C8 (wz b); C8 (wz c)])
      by (eapply rw_cells_transport; [exact CV2 | exact MU4 | exact WM4 | cbn; unfold AINTRIN_STACK; lia]).
    assert (SV4 : SHAD m4 (st + 216) (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV2 | exact MU4 | exact WM4 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      assert (sh (st + 216) + 3 <= 0x10007fff8000) by (unfold sh, ASHADOW_BASE; unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA; Z.div_mod_to_equations; lia).
      assert (SHV : sh (st + 216) + 3 <= sh b \/ sh b + nsh (c - b) <= sh (st + 216)).
      { clear - VBD V8 B16 BE. unfold sh, nsh. Z.div_mod_to_equations. nia. }
      unfold AINTRIN_STACK. lia. }
    assert (S04 : stack0 m4 lo shi).
    { eapply stack0_transport; [exact S02 | exact MU4 | exact WM4 |].
      apply Forall_cons; [right; cbn; exact SPA|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO, AINTRIN_STACK; lia | apply Forall_nil]. }

    lazymatch goal with |- evt _ _ (MS ?T _ _ _ _ _ _) => remember T as R3 eqn:HR3 end.
    pose (E3 := Eseed R3 [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 b; Z_to_bv 64 c]).
    assert (HR3s : regs_ok E3 (srs sr_id HTbAHStDtV_1) R3).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R3; evs; try reflexivity;
        unfold shw; rewrite ?w_addm, ?w_add by lia; reflexivity. }
    assert (GZV4 : gz m4 (st + 216) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV4 | cbn; lia]).
    assert (HK3 : know_ok asegs E3 m4
       (kn_fix 20 [AOPDEL2] (SCR [] [] []) DV3_A2
          (srs sr_id HTbAHStDtV_1)
       [ KWord (SA (EVar 32) 216) 8 (EVar 34); KWord (SA (EVar 32) 232) 8 (EVar 35);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47); KRange (EVar 34) 0x6e6000 (2 ^ 47) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CV4 0%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV4 16%nat (C8 (wz c)). }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R3 DV3_A2 m4 (seg_rom asegs) HR3s HK3 200%nat [AOPDEL2] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E3 VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 SB0 SB1' SB2'.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: first [ sc_shdj | sc_dj ]. }
    clear HK3.
    assert (HF3 : rfull R3) by (rewrite HR3; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF3) as HF3'. cbn [ms_regs] in HF3'.
    readback HR' HF3' HR3 HRe3.
    rreg HR' 1%bv J1. rreg HR' 10%bv J10. rreg HR' 11%bv J11.
    rreg HR' 2%bv J2. rreg HR' 8%bv J8. rreg HR' 9%bv J9. rreg HR' 18%bv J18. rreg HR' 19%bv J19. rreg HR' 20%bv J20.
    rreg HR' 21%bv J21. rreg HR' 22%bv J22. rreg HR' 23%bv J23.
    rewrite ?w_add in J9, J18, J19, J21, J22, J23 by lia. rewrite w_negadd in J11 by lia.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe3, J1, J10, J11, J2, J8, J9, J18, J19, J20, J21, J22, J23.
    apply evt_done.
    do 14 eexists. split; [reflexivity|].
    split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|]. split; [exact ST4|].
    split; [exact SH4|]. split; [exact AC4|]. split; [exact S04 | exact CV4].
  Qed.
End DtV3b.

Section DtV3c.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HANN : annotate_gen_stmt.
  Hypothesis HCF : forall n, as_Cf H n = 0.

  Definition dv3_pre (x24 x25 x26 x27 gp tp : word) (F : bvmap 5 word) (fc : bv 32) (st spf b c lo shi : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists w5 w6 w7 a2' a3' a4' a5' a6' a7' w28 w29 w30 w31 m1,
      ms' = MS (mkR (Z_to_bv 64 DV3_N) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 216))
                    (Z_to_bv 64 b) (Z_to_bv 64 (c - b)) a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (st + 232)) (Z_to_bv 64 (st + 224)) (Z_to_bv 64 0x7fff8000)
                    (shw (st + 216)) (shw (st + 232)) (shw (st + 224)) x24 x25 x26 x27 w28 w29 w30 w31)
               F (Z_to_bv 64 AOPDEL2) fc None m1 (seg_rom asegs)
      /\ munch [(st + 224, st + 232); (sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)] m m1
      /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo spf
      /\ SHAD m1 b (shadow_of (c - b)) /\ ACONST m1 /\ stack0 m1 lo shi
      /\ rw_cells asegs m1 (st + 216) [C8 (wz b); C8 (wz b); C8 (wz c)].

  Lemma dv3_pre_evt : forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (st spf b e c lo shi : Z),
    rw_cells asegs m (st + 216) [C8 (wz b); C8 (wz e); C8 (wz c)] -> SHAD m (st + 216) (repeat (b8 0) 3) -> st mod 8 = 0 ->
    aapp st ST_SIZE ->
    b <> 0 -> aapp b (c - b) -> b mod 16 = 0 -> b <= e <= c -> c - b <= 2 ^ 40 ->
    SHAD m b (cc_gen (c - b) (e - b)) -> (c <= st + 216 \/ st + 240 <= b) ->
    stack0 m lo shi -> spf <= shi ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (dv3_pre x24 x25 x26 x27 gp tp F fc st spf b c lo shi m)
      (MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 (Z_to_bv 64 st) x11 x12 x13 x14 x15 x16 x17 x18 x19
               (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 DV3) fc None m (seg_rom asegs)).
  Proof.
    intros until shi. intros CV SV V8 VA0 B0 BA B16 BE BL SB VBD S0 SHI ST CE LO SP16 SPR MI AC.
    eapply evt_cut; [eapply (dv3_a HANN); eassumption|].
    intros ms2 (w5 & w6 & w7 & d10 & d11 & d12 & d13 & d14 & d15 & d16 & d17 & w28 & w29 & w30 & w31 & m2 & EQ & MU & WM & MI2 & ST2
                & CV2 & SV2 & S02 & SH2 & AC2).
    subst ms2.
    eapply evt_mono; [eapply (dv3_b HANN); try eassumption; lia|].
    intros ms' (t5 & t6 & t7 & a2' & a3' & a4' & a5' & a6' & a7' & t28 & t29 & t30 & t31 & m' & EQ' & MU' & WM' & MI' & ST' & SH'
                & AC' & S0' & CV').
    exists t5, t6, t7, a2', a3', a4', a5', a6', a7', t28, t29, t30, t31, m'.
    split; [exact EQ'|].
    split.
    { eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU MU')].
      intros x Hx; cbn [app outside] in Hx |- *; clear - Hx; lia. }
    split; [exact (wmono_trans asegs _ _ _ WM WM')|].
    repeat (split; [assumption|]). assumption.
  Qed.

  Lemma dtv3 : forall (Q : config -> Prop)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (LF : list fframe)
      (st spf lo B shi : Z) (errv : word) (mo : Model) (pid : bptr) (b e c : Z),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 (Z_to_bv 64 st) x11 x12 x13 x14 x15 x16 x17 x18 x19
                             (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DV3) fc None m (seg_rom asegs) ->
    rw_cells asegs m (st + 216) [C8 (wz b); C8 (wz e); C8 (wz c)] -> SHAD m (st + 216) (repeat (b8 0) 3) -> st mod 8 = 0 ->
    (b = 0 -> e = 0 /\ c = 0) ->
    (aapp st ST_SIZE \/ (spf <= st /\ st + ST_SIZE + 64 <= shi)) ->
    (b <> 0 -> In (pid, b, c - b) LB /\ b <= e <= c /\ c - b <= 2 ^ 40 /\ SHAD m b (cc_gen (c - b) (e - b))
               /\ (c <= st + 216 \/ st + 240 <= b) /\ st_live_frame LF st) ->
    lb_own LB m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m -> as_RFS H LF m -> stack0 m lo shi -> spf <= shi ->
    (b <> 0 -> trace_ok (as_TR H) APC0_FREE [DV3_N]) ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H)
            (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y23 y28 y29 y30 y31 : word),
       as_VIS H s' msF' = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                                 (Z_to_bv 64 0x7fff8000) y21 y22 y23 x24 x25 x26 x27 y28 y29 y30 y31)
                             F (Z_to_bv 64 DV3_N) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr tp) [C4 errv] -> as_rauxv_ok H m' B ->
       ACONST m' -> as_RFS H LF m' -> stack0 m' lo shi ->
       as_RHEAP H s' (dv_LB H LB pid b) m' -> lb_own (dv_LB H LB pid b) m' ->
       xpres H (dv_LB H LB pid b) spf [(st + 216, st + 240)] m m' -> as_AL H s' >= as_AL H s ->
       wr_at asegs m' (st + 216) 24 ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp
      F fc msF m s LB LF st spf lo B shi errv mo pid b e c VIS CV SV V8 B0E HLOC B1P OWN RH KR AL0 RA SPB ST CE LO ERR MI TP SP16 SPR
      AC RF S0 SHI TRC K.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK FR]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4). unfold AIMG_TOP in FS1.
    unfold AFREE_STACK, ST_SIZE in *.
    assert (STB : 0x6e6000 <= st /\ st + 240 <= 2 ^ 47).
    { destruct HLOC as [HA|[HS1 HS2]]; [pose proof (aapp_bounds st 240 HA ltac:(lia)) as (X1 & X2 & X3 & _); unfold AIMG_TOP, AAPP_HI in *; lia | lia]. }
    destruct (Z.eq_dec b 0) as [Bz | Bnz].
    -
      destruct (B0E Bz) as [E1 C1]. subst b e c.
      remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 (Z_to_bv 64 st) x11 x12 x13 x14 x15 x16 x17 x18 x19
                 (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtV_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (GZV : gz m (st + 216) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DV3_N] (SCR [] [] []) DV3 (srs sr_id HTbAHStDtV_0)
         [ KWord (SA (EVar 32) 216) 8 (ELit 0);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DV3 m (seg_rom asegs) HR HK 200%nat [DV3_N] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      eapply (sr_blk H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1.
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 20%bv G20.
      rewrite HRe in VIS1. cbn [getr] in VIS1. rewrite ?G2, ?G8, ?G20 in VIS1.
      eapply K; [exact VIS1 | exact KR1 | exact MP1 | exact MI | exact ST | exact ERR | exact RA | exact AC | exact RF | exact S0
                | unfold dv_LB; rewrite Z.eqb_refl; exact RH | unfold dv_LB; rewrite Z.eqb_refl; exact OWN
                | apply xpres_refl | lia | exact (rw_cells_wr_at _ _ _ _ 24 CV ltac:(cbn; lia))].
    -
      destruct (B1P Bnz) as (INB & BE & BL & SB & BDV & (fv & INV & FV1 & FV2)). unfold ST_SIZE in FV1, FV2.
      pose proof (FR fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
      pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
      assert (VA0 : aapp st 240) by (eapply aapp_sub; [exact FS4 | unfold AFS_SIZE; lia | unfold AFS_SIZE; lia]).
      pose proof (aapp_bounds st 240 VA0 ltac:(lia)) as (SA1 & SA2 & SA3 & SA4 & SA5). unfold AIMG_TOP, AAPP_HI in SA1, SA3.
      pose proof (ah_blocks H HH _ _ _ _ RH INB) as ABR. unfold blk_addr, blk_size in ABR. cbn [fst snd] in ABR.
      pose proof ABR as (BB0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
      assert (SPH : sh b + nsh (c - b) <= 0x10007fff8000)
        by (pose proof (sh_nsh_high b (c - b) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
      assert (SHL : 0x7fff8000 <= sh b) by (unfold sh, ASHADOW_BASE; pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)); lia).
      assert (SPA : sh b + nsh (c - b) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).

      eapply (ahh_evt_then H HH (dv3_pre x24 x25 x26 x27 gp tp F fc st spf b c lo shi m)); [exact KR | exact VIS | |].
      { eapply dv3_pre_evt; try eassumption; unfold ST_SIZE, AFREE_STACK in *; lia. }
      intros msF1 mo1 KR1 MP1 (t5 & t6 & t7 & a2' & a3' & a4' & a5' & a6' & a7' & t28 & t29 & t30 & t31 & m1 & VIS1 & MU1 & WM1 & MI1
                                & ST1 & SH1 & AC1 & S01 & CV1).
      assert (W1 : Forall (fun iv : Z * Z => aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv)
                     [(st + 224, st + 232); (sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)]).
      { apply Forall_cons.
        { split; [right; right; right; right; left; cbn; unfold AFS_SIZE in *; lia|].
          split; [right; exists fv; split; [exact INV | cbn; lia]|].
          eapply (aconst_ok_app st 240); [exact VA0 | cbn; lia | cbn; lia]. }
        apply Forall_cons.
        { split; [right; right; right; left; exists (pid, b, c - b); split; [exact INB | cbn; lia]|].
          split.
          { left. cbn. pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE b (c - b) FS4 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S.
            unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. split; lia. }
          apply aconst_ok_high; [cbn [fst snd]; apply sh_mono; unfold AIMG_TOP; lia | right; left; cbn; lia]. }
        apply Forall_cons; [| apply Forall_nil].
        split; [left; cbn; unfold AINTRIN_STACK; lia|]. split; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AINTRIN_STACK in *; split; lia|].
        apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity; cbn; unfold AINTRIN_STACK; lia | right; left; cbn; unfold AINTRIN_STACK; lia]. }
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv) => proj1 K) W1) as W1C.
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv) => proj1 (proj2 K)) W1) as W1F.
      assert (RH1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W1C]).
      assert (RA1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | exact W1C]).
      assert (RF1 : as_RFS H LF m1) by (eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 | exact W1F]).
      assert (ERR1 : rw_cells asegs m1 (errno_addr tp) [C4 errv]).
      { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
        eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP, AINTRIN_STACK; lia]. }
      pose proof (lb_own_wmono _ _ _ OWN WM1) as OWN1.
      destruct (rw_cells_of_own LB m1 (pid, b, c - b) OWN1 INB ltac:(cbn; unfold AIMG_TOP; lia) ltac:(cbn; lia)) as (bs & CB1).
      cbn [blk_addr blk_size fst snd] in CB1.

      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (LB := LB) (p := pid) (A := b) (n := c - b) (lo := lo) (B := B) (errv := errv) (CH := [])
                                     (sbs := shadow_of (c - b)) (bs := bs);
          [exact VIS1 | exact RH1 | exact KR1 | exact INB | rewrite HCF; exact AL0 | exact CB1 | exact SH1 | rewrite shadow_of_length by lia; reflexivity
          | exact RA1 | rewrite u64_of_Z by lia; lia | rewrite u64_of_Z by lia; exact ST1
          | exact CE | rewrite u64_of_Z by lia; unfold AFREE_STACK; lia | exact ERR1 | exact MI1 | exact TP
          | rewrite u64_of_Z by lia; exact SP16 | exact AC1
          | rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; lia
          | rewrite u64_of_Z by (unfold DV3_N; lia); exact (TRC Bnz) | reflexivity ]. }
      intros [msF2 mo2] POST2.
      destruct POST2 as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & sA
                         & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & RH2 & AC2 & AL2).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite u64_of_Z in ST2, AP2 by lia.
      rewrite (ret_pc_even DV3_N ltac:(unfold DV3_N; lia) eq_refl) in VIS2.
      set (LB' := as_lb_remove H pid LB) in *.

      assert (FRM : forall a, 0 <= a < 2 ^ 64 -> (as_FSB H <= a < as_FSB H + AFS_SIZE \/ ATLS_PRIV_LO <= a < ATLS_PRIV_HI
                               \/ sh (as_FSB H) <= a < sh (as_FSB H + AFS_SIZE)) ->
                     m2 (wa a) = m1 (wa a) /\ (wview asegs m1 (wa a) <> None -> wview asegs m2 (wa a) <> None)).
      { intros a Ha Hr. apply (AP2 a Ha). unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
        - right; right; right; right; left; exact Hr.
        - right; left. unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. right; right; right; lia.
        - right; right; right; right; right; left; exact Hr. }
      assert (RF2 : as_RFS H LF m2) by (eapply (ah_RFS_ext H HH); [exact RF1 | exact FRM]).
      assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]).
      assert (OWN2 : lb_own LB' m2).
      { pose proof (ah_lb_remove H HH) as (_ & _ & L3).
        eapply (lb_own_apres H); [exact (lb_own_incl LB _ m1 (L3 pid LB) OWN1) | exact AP2 | intros bb Hb; exact Hb]. }
      assert (XP : xpres H LB' spf [(st + 216, st + 240)] m m2).
      { apply (xpres_drop_blk H HH s LB pid b (c - b) spf [(st + 216, st + 240)] m m m2 RH INB ltac:(lia)).
        eapply xpres_trans.
        { eapply (xpres_of_munch H sA LB' spf _ _ m2 m m1); [exact HH | exact RH2 | exact MU1 | exact WM1 |].
          apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia|].
          apply Forall_cons; [right; intros a Ha; cbn; right; right; left; cbn in Ha; lia|].
          apply Forall_cons; [left; cbn; unfold AINTRIN_STACK; lia | apply Forall_nil]. }
        exact (xpres_of_apres H _ _ _ _ _ AP2). }
      assert (WO : wr_at asegs m2 (st + 216) 24).
      { pose proof (wr_at_wmono _ _ _ _ (rw_cells_wr_at _ _ _ _ 24 CV ltac:(cbn; lia)) WM1) as (P0 & P1 & PW).
        split; [exact P0|]. split; [exact P1|]. intros i Hi.
        apply (proj2 (FRM (st + 216 + i) ltac:(lia) ltac:(left; unfold AFS_SIZE in *; lia))). apply PW. exact Hi. }
      eapply K; [exact VIS2 | exact KR2 | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2] | exact MI2 | exact ST2
                | exact ERR2 | exact RA2 | exact AC2 | exact RF2 | exact S02
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq b 0) Bnz); exact RH2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq b 0) Bnz); exact OWN2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq b 0) Bnz); exact XP
                | rewrite HCF in AL2; lia | exact WO].
  Qed.
End DtV3c.

Definition DV2 : Z := 0xeb068.  Definition DV2_A1 : Z := 0xeb0c0.  Definition DV2_A2 : Z := 0xeb0f0.  Definition DV2_N : Z := 0xeb110.

Section DtV2.
  Context {HCEIL : HeapCeil}.
  Hypothesis HANN : annotate_gen_stmt.

  Definition dv2_mid1 (x24 x25 x26 x27 gp tp : word) (F : bvmap 5 word) (fc : bv 32) (st spf b c lo shi : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists w5 w6 w7 d10 d11 d12 d13 d14 d15 d16 d17 w28 w29 w30 w31 m2,
      ms' = MS (mkR (Z_to_bv 64 DV2_A1) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 192))
                    d10 d11 d12 d13 d14 d15 d16 d17 (Z_to_bv 64 (st + 208)) (Z_to_bv 64 (st + 200)) (Z_to_bv 64 0x7fff8000)
                    (shw (st + 192)) (shw (st + 208)) (shw (st + 200)) x24 x25 x26 x27 w28 w29 w30 w31)
               F (Z_to_bv 64 DV2_A1) fc None m2 (seg_rom asegs)
      /\ munch [(st + 200, st + 208); (sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)] m m2
      /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo spf
      /\ rw_cells asegs m2 (st + 192) [C8 (wz b); C8 (wz b); C8 (wz c)]
      /\ SHAD m2 (st + 192) (repeat (b8 0) 3) /\ stack0 m2 lo shi /\ SHAD m2 b (cc_gen (c - b) 0) /\ ACONST m2.

#[local] Definition HTbAHStDtV_2 : list (reg * expr) := [(8%bv, EVar 32); (2%bv, EVar 33); (20%bv, ELit 2147450880)].
  Lemma dv2_a : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (st spf b e c lo shi : Z),
    rw_cells asegs m (st + 192) [C8 (wz b); C8 (wz e); C8 (wz c)] -> SHAD m (st + 192) (repeat (b8 0) 3) -> st mod 8 = 0 ->
    aapp st ST_SIZE ->
    b <> 0 -> aapp b (c - b) -> b mod 16 = 0 -> b <= e <= c -> c - b <= 2 ^ 40 ->
    SHAD m b (cc_gen (c - b) (e - b)) -> (c <= st + 192 \/ st + 216 <= b) ->
    stack0 m lo shi -> spf <= shi ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (dv2_mid1 x24 x25 x26 x27 gp tp F fc st spf b c lo shi m)
      (MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 DV2) fc None m (seg_rom asegs)).
  Proof.
    intros until shi. intros CV SV V8 VA0 B0 BA B16 BE BL SB VBD S0 SHI ST CE LO SP16 SPR MI AC.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VA : aapp (st + 192) 24) by (eapply aapp_sub; [exact VA0 | lia | unfold ST_SIZE; lia]).
    pose proof (aapp_bounds st ST_SIZE VA0 ltac:(unfold ST_SIZE; lia)) as (SB1' & SB2' & SB3' & SB4' & SB5').
    unfold AFREE_STACK, ST_SIZE, AIMG_TOP in *.
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (aapp_bounds (st + 192) 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5).
    pose proof (aapp_bounds b (c - b) BA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
    unfold AIMG_TOP in VB1, PB1.
    remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 b; Z_to_bv 64 e; Z_to_bv 64 c]).
    assert (HR : regs_ok E (srs sr_id HTbAHStDtV_2) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (GZV : gz m (st + 192) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
    assert (HK : know_ok asegs E m
       (kn_fix 20 [AANNOTATE_CC] (SCR [] [] []) DV2 (srs sr_id HTbAHStDtV_2)
       [ KWord (SA (EVar 32) 192) 8 (EVar 34); KWord (SA (EVar 32) 200) 8 (EVar 35); KWord (SA (EVar 32) 208) 8 (EVar 36);
         KWr (SA (EVar 32) 192) (ELit 24);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47); KRange (EVar 34) 0x6e6000 (2 ^ 47) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV 8%nat (C8 (wz e)). }
      apply Forall_cons. { kword_cell CV 16%nat (C8 (wz c)). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact (proj2 CV) | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R DV2 m (seg_rom asegs) HR HK 200%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 SB0 SB1' SB2'.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: first [ sc_shdj | sc_dj ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rreg HR' 12%bv L12. rreg HR' 13%bv L13. rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23.
    rewrite ?w_add in L9, L18, L19, L21, L22, L23 by lia.

    assert (WV1 : forall a, st + 192 <= a -> a + 8 <= st + 216 -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (proj2 CV) as W. destruct W as (W1 & W2 & W). cbn [cells_size csize Z.of_nat] in W.
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (st + 192 + (a - (st + 192) + i)) by lia. apply W. cbn. lia. }
    assert (MU1 : munch [(st + 200, st + 208)] m M1).
    { subst M1. clear - Hlf VB1 VB2 VB3 SPR LO CE ACF1 ACF2. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spf) by (subst M1; apply stk_mem_denot; exact ST).
    assert (SVP : sh b + nsh (c - b) <= st + 192 \/ st + 216 <= sh b)
      by (pose proof (aapp_disjoint_sh (st + 192) 24 b (c - b) VA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)); lia).
    assert (SPH : sh b + nsh (c - b) <= 0x10007fff8000)
      by (pose proof (sh_nsh_high b (c - b) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
    assert (SPA : sh b + nsh (c - b) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHV : sh (st + 192) + 3 <= sh b \/ sh b + nsh (c - b) <= sh (st + 192)).
    { clear - VBD V8 B16 BE. unfold sh, nsh. Z.div_mod_to_equations. nia. }
    assert (SB1 : SHAD M1 b (cc_gen (c - b) (e - b))).
    { eapply SHAD_transport; [exact SB | exact MU1 | exact WM1 |]. rewrite cc_gen_length by lia. cbn. lia. }
    assert (SV1 : SHAD M1 (st + 192) (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV | exact MU1 | exact WM1 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      unfold sh, ASHADOW_BASE. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA. Z.div_mod_to_equations. lia. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [eapply (stack0_ok_aapp (st + 192) 24); [exact VA | cbn; lia | cbn; lia] | apply Forall_nil]. }
    assert (AC1 : ACONST M1).
    { eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |].
      apply Forall_cons; [eapply (aconst_ok_app (st + 192) 24); [exact VA | cbn; lia | cbn; lia] | apply Forall_nil]. }
    assert (CV1 : rw_cells asegs M1 (st + 192) [C8 (wz b); C8 (wz b); C8 (wz c)]).
    { change [C8 (wz b); C8 (wz e); C8 (wz c)] with ([C8 (wz b)] ++ [C8 (wz e)] ++ [C8 (wz c)]) in CV.
      apply rw_cells_app in CV as [CV0 CV']. apply rw_cells_app in CV' as [_ CV2].
      replace (st + 192 + Z.of_nat (cells_size [C8 (wz b)]) + Z.of_nat (cells_size [C8 (wz e)])) with (st + 208) in CV2 by (cbn; lia).
      apply rw_cells_cons8_c.
      { eapply rw_cells_transport; [exact CV0 | exact MU1 | exact WM1 | cbn; lia]. }
      apply rw_cells_cons8_c.
      { subst M1. clear - Hlf WV1 VB1 VB2 VB3 SPR LO CE ACF1 ACF2. replace (st + 192 + 8) with (st + 200) by lia.
        lgcell Hlf (WV1 (st + 200) ltac:(lia) ltac:(lia)) 0%nat. }
      replace (st + 192 + 8 + 8) with (st + 208) by lia.
      eapply rw_cells_transport; [exact CV2 | exact MU1 | exact WM1 | cbn; lia]. }

    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L8, L9, L10, L11, L12, L13, L18, L19, L20, L21, L22, L23.
    clear HRe HR' Hlf Hms HF1 L1 L2 L8 L9 L10 L11 L12 L13 L18 L19 L20 L21 L22 L23.
    eapply evt_cut.
    { eapply HANN with (beg := b) (len := c - b) (oldmid := e - b) (newmid := 0) (lo := lo); rewrite ?u64_of_Z by lia.
      - reflexivity.
      - f_equal; lia.
      - f_equal; lia.
      - rewrite Z.add_0_r. reflexivity.
      - Z.div_mod_to_equations; lia.
      - lia.
      - lia.
      - lia.
      - exact BA.
      - unfold AAPP_HI; lia.
      - exact SB1.
      - exact ST1.
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact MI1.
      - exact AC1.
      - eapply aapp_in_app_mem; [exact BA | lia | lia]. }
    intros ms2 POST2.
    destruct POST2 as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m2 & EQ2 & MU2 & WM2 & MI2 & ST2 & SH2 & AC2).
    subst ms2. rewrite u64_of_Z in MU2, ST2 by lia.
    rewrite (ret_pc_even 962752 ltac:(lia) eq_refl).
    assert (CV2 : rw_cells asegs m2 (st + 192) [C8 (wz b); C8 (wz b); C8 (wz c)])
      by (eapply rw_cells_transport; [exact CV1 | exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; lia]).
    assert (SV2 : SHAD m2 (st + 192) (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV1 | exact MU2 | exact WM2 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      assert (sh (st + 192) + 3 <= 0x10007fff8000) by (unfold sh, ASHADOW_BASE; unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA; Z.div_mod_to_equations; lia).
      unfold AINTRIN_STACK. lia. }
    assert (S02 : stack0 m2 lo shi).
    { eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 |].
      apply Forall_cons; [right; cbn; exact SPA|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO, AINTRIN_STACK; lia | apply Forall_nil]. }
    apply evt_done. exists w0, w1, w2, d0, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m2.
    split; [reflexivity|].
    split; [exact (munch_app _ _ _ _ _ MU1 MU2)|].
    split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact CV2|].
    split; [exact SV2|]. split; [exact S02|]. split; [exact SH2 | exact AC2].
  Qed.
End DtV2.

Section DtV2b.
  Context {HCEIL : HeapCeil}.
  Hypothesis HANN : annotate_gen_stmt.

  Definition dv2_del (x24 x25 x26 x27 gp tp : word) (F : bvmap 5 word) (fc : bv 32) (st spf b c lo shi : Z) (m2 : mem)
      : machine_state -> Prop :=
    fun ms' => exists w5 w6 w7 a2' a3' a4' a5' a6' a7' w28 w29 w30 w31 m',
      ms' = MS (mkR (Z_to_bv 64 DV2_N) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 192))
                    (Z_to_bv 64 b) (Z_to_bv 64 (c - b)) a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (st + 208)) (Z_to_bv 64 (st + 200)) (Z_to_bv 64 0x7fff8000)
                    (shw (st + 192)) (shw (st + 208)) (shw (st + 200)) x24 x25 x26 x27 w28 w29 w30 w31)
               F (Z_to_bv 64 AOPDEL2) fc None m' (seg_rom asegs)
      /\ munch [(sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)] m2 m'
      /\ wmono asegs m2 m' /\ mem_inv asegs m' /\ stk asegs m' lo spf
      /\ SHAD m' b (shadow_of (c - b)) /\ ACONST m' /\ stack0 m' lo shi
      /\ rw_cells asegs m' (st + 192) [C8 (wz b); C8 (wz b); C8 (wz c)].

#[local] Definition HTbAHStDtV_3 : list (reg * expr) := [(2%bv, EVar 33); (8%bv, EVar 32); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 192)); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 208)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 200)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 192)) (ELit 3)) (ELit 2147450880)); (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 208)) (ELit 3)) (ELit 2147450880)); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 200)) (ELit 3)) (ELit 2147450880))].
  Lemma dv2_b : forall (w5 w6 w7 d10 d11 d12 d13 d14 d15 d16 d17 x24 x25 x26 x27 w28 w29 w30 w31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (m2 : mem) (st spf b c lo shi : Z),
    stk asegs m2 lo spf -> mem_inv asegs m2 ->
    rw_cells asegs m2 (st + 192) [C8 (wz b); C8 (wz b); C8 (wz c)] ->
    SHAD m2 (st + 192) (repeat (b8 0) 3) -> stack0 m2 lo shi -> SHAD m2 b (cc_gen (c - b) 0) -> ACONST m2 ->
    st mod 8 = 0 -> aapp st ST_SIZE ->
    b <> 0 -> aapp b (c - b) -> b mod 16 = 0 -> b <= c -> c - b <= 2 ^ 40 -> (c <= st + 192 \/ st + 216 <= b) ->
    spf <= shi ->
    aceil <= lo -> lo <= spf - AFREE_STACK -> spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 ->
    evt asegs (dv2_del x24 x25 x26 x27 gp tp F fc st spf b c lo shi m2)
      (MS (mkR (Z_to_bv 64 DV2_A1) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 192))
               d10 d11 d12 d13 d14 d15 d16 d17 (Z_to_bv 64 (st + 208)) (Z_to_bv 64 (st + 200)) (Z_to_bv 64 0x7fff8000)
               (shw (st + 192)) (shw (st + 208)) (shw (st + 200)) x24 x25 x26 x27 w28 w29 w30 w31)
          F (Z_to_bv 64 DV2_A1) fc None m2 (seg_rom asegs)).
  Proof.
    intros until shi. intros ST2 MI2 CV2 SV2 S02 SH2 AC2 V8 VA0 B0 BA B16 BE BL VBD SHI CE LO SP16 SPR.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VA : aapp (st + 192) 24) by (eapply aapp_sub; [exact VA0 | lia | unfold ST_SIZE; lia]).
    pose proof (aapp_bounds st ST_SIZE VA0 ltac:(unfold ST_SIZE; lia)) as (SB1' & SB2' & SB3' & SB4' & SB5').
    unfold AFREE_STACK, ST_SIZE, AIMG_TOP in *.
    pose proof (stack0_bounds m2 lo shi S02) as SB0. unfold AAPP_HI in SB0.
    pose proof (aapp_bounds (st + 192) 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5).
    pose proof (aapp_bounds b (c - b) BA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
    unfold AIMG_TOP in VB1, PB1.
    assert (SVP : sh b + nsh (c - b) <= st + 192 \/ st + 216 <= sh b)
      by (pose proof (aapp_disjoint_sh (st + 192) 24 b (c - b) VA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)); lia).
    assert (SPH : sh b + nsh (c - b) <= 0x10007fff8000)
      by (pose proof (sh_nsh_high b (c - b) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
    assert (SPA : sh b + nsh (c - b) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).

    lazymatch goal with |- evt _ _ (MS ?T _ _ _ _ _ _) => remember T as R2 eqn:HR2 end.
    pose (E2 := Eseed R2 [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 b; Z_to_bv 64 c]).
    assert (HR2s : regs_ok E2 (srs sr_id HTbAHStDtV_3) R2).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R2; evs; try reflexivity;
        unfold shw; rewrite ?w_addm, ?w_add by lia; reflexivity. }
    assert (GZV2 : gz m2 (st + 192) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV2 | cbn; lia]).
    assert (HK2 : know_ok asegs E2 m2
       (kn_fix 20 [AANNOTATE_CC] (SCR [] [] []) DV2_A1
          (srs sr_id HTbAHStDtV_3)
       [ KWord (SA (EVar 32) 192) 8 (EVar 34); KWord (SA (EVar 32) 200) 8 (EVar 34); KWord (SA (EVar 32) 208) 8 (EVar 35);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47); KRange (EVar 34) 0x6e6000 (2 ^ 47) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CV2 0%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV2 8%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV2 16%nat (C8 (wz c)). }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R2 DV2_A1 m2 (seg_rom asegs) HR2s HK2 200%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E2 VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 SB0 SB1' SB2'.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: first [ sc_shdj | sc_dj ]. }
    clear HK2.
    assert (HF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF2) as HF2'. cbn [ms_regs] in HF2'.
    readback HR' HF2' HR2 HRe2.
    rreg HR' 1%bv K1. rreg HR' 10%bv K10. rreg HR' 11%bv K11. rreg HR' 12%bv K12. rreg HR' 13%bv K13.
    rreg HR' 2%bv K2. rreg HR' 8%bv K8. rreg HR' 9%bv K9. rreg HR' 18%bv K18. rreg HR' 19%bv K19. rreg HR' 20%bv K20.
    rreg HR' 21%bv K21. rreg HR' 22%bv K22. rreg HR' 23%bv K23.
    rewrite ?w_add in K9, K18, K19, K21, K22, K23 by lia.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe2, K1, K10, K11, K12, K13, K2, K8, K9, K18, K19, K20, K21, K22, K23.
    clear HRe2 HR' Hlf Hms HF2' K1 K10 K11 K12 K13 K2 K8 K9 K18 K19 K20 K21 K22 K23.

    eapply evt_cut.
    { eapply HANN with (beg := b) (len := c - b) (oldmid := 0) (newmid := c - b) (lo := lo); rewrite ?u64_of_Z by lia.
      - reflexivity.
      - f_equal; lia.
      - rewrite Z.add_0_r. reflexivity.
      - f_equal; lia.
      - Z.div_mod_to_equations; lia.
      - lia.
      - lia.
      - lia.
      - exact BA.
      - unfold AAPP_HI; lia.
      - exact SH2.
      - exact ST2.
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact MI2.
      - exact AC2.
      - eapply aapp_in_app_mem; [exact BA | lia | lia]. }
    intros ms4 POST4.
    destruct POST4 as (v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m4 & EQ4 & MU4 & WM4 & MI4 & ST4 & SH4 & AC4).
    subst ms4. rewrite u64_of_Z in MU4, ST4 by lia.
    rewrite (ret_pc_even 962800 ltac:(lia) eq_refl).
    rewrite cc_gen_full in SH4.

    assert (CV4 : rw_cells asegs m4 (st + 192) [C8 (wz b); C8 (wz b); C8 (wz c)])
      by (eapply rw_cells_transport; [exact CV2 | exact MU4 | exact WM4 | cbn; unfold AINTRIN_STACK; lia]).
    assert (SV4 : SHAD m4 (st + 192) (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV2 | exact MU4 | exact WM4 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      assert (sh (st + 192) + 3 <= 0x10007fff8000) by (unfold sh, ASHADOW_BASE; unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA; Z.div_mod_to_equations; lia).
      assert (SHV : sh (st + 192) + 3 <= sh b \/ sh b + nsh (c - b) <= sh (st + 192)).
      { clear - VBD V8 B16 BE. unfold sh, nsh. Z.div_mod_to_equations. nia. }
      unfold AINTRIN_STACK. lia. }
    assert (S04 : stack0 m4 lo shi).
    { eapply stack0_transport; [exact S02 | exact MU4 | exact WM4 |].
      apply Forall_cons; [right; cbn; exact SPA|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO, AINTRIN_STACK; lia | apply Forall_nil]. }

    lazymatch goal with |- evt _ _ (MS ?T _ _ _ _ _ _) => remember T as R3 eqn:HR3 end.
    pose (E3 := Eseed R3 [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 b; Z_to_bv 64 c]).
    assert (HR3s : regs_ok E3 (srs sr_id HTbAHStDtV_3) R3).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R3; evs; try reflexivity;
        unfold shw; rewrite ?w_addm, ?w_add by lia; reflexivity. }
    assert (GZV4 : gz m4 (st + 192) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV4 | cbn; lia]).
    assert (HK3 : know_ok asegs E3 m4
       (kn_fix 20 [AOPDEL2] (SCR [] [] []) DV2_A2
          (srs sr_id HTbAHStDtV_3)
       [ KWord (SA (EVar 32) 192) 8 (EVar 34); KWord (SA (EVar 32) 208) 8 (EVar 35);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47); KRange (EVar 34) 0x6e6000 (2 ^ 47) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CV4 0%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV4 16%nat (C8 (wz c)). }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R3 DV2_A2 m4 (seg_rom asegs) HR3s HK3 200%nat [AOPDEL2] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E3 VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 SB0 SB1' SB2'.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: first [ sc_shdj | sc_dj ]. }
    clear HK3.
    assert (HF3 : rfull R3) by (rewrite HR3; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF3) as HF3'. cbn [ms_regs] in HF3'.
    readback HR' HF3' HR3 HRe3.
    rreg HR' 1%bv J1. rreg HR' 10%bv J10. rreg HR' 11%bv J11.
    rreg HR' 2%bv J2. rreg HR' 8%bv J8. rreg HR' 9%bv J9. rreg HR' 18%bv J18. rreg HR' 19%bv J19. rreg HR' 20%bv J20.
    rreg HR' 21%bv J21. rreg HR' 22%bv J22. rreg HR' 23%bv J23.
    rewrite ?w_add in J9, J18, J19, J21, J22, J23 by lia. rewrite w_negadd in J11 by lia.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe3, J1, J10, J11, J2, J8, J9, J18, J19, J20, J21, J22, J23.
    apply evt_done.
    do 14 eexists. split; [reflexivity|].
    split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|]. split; [exact ST4|].
    split; [exact SH4|]. split; [exact AC4|]. split; [exact S04 | exact CV4].
  Qed.
End DtV2b.

Section DtV2c.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HANN : annotate_gen_stmt.
  Hypothesis HCF : forall n, as_Cf H n = 0.

  Definition dv2_pre (x24 x25 x26 x27 gp tp : word) (F : bvmap 5 word) (fc : bv 32) (st spf b c lo shi : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists w5 w6 w7 a2' a3' a4' a5' a6' a7' w28 w29 w30 w31 m1,
      ms' = MS (mkR (Z_to_bv 64 DV2_N) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 192))
                    (Z_to_bv 64 b) (Z_to_bv 64 (c - b)) a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (st + 208)) (Z_to_bv 64 (st + 200)) (Z_to_bv 64 0x7fff8000)
                    (shw (st + 192)) (shw (st + 208)) (shw (st + 200)) x24 x25 x26 x27 w28 w29 w30 w31)
               F (Z_to_bv 64 AOPDEL2) fc None m1 (seg_rom asegs)
      /\ munch [(st + 200, st + 208); (sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)] m m1
      /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo spf
      /\ SHAD m1 b (shadow_of (c - b)) /\ ACONST m1 /\ stack0 m1 lo shi
      /\ rw_cells asegs m1 (st + 192) [C8 (wz b); C8 (wz b); C8 (wz c)].

  Lemma dv2_pre_evt : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (st spf b e c lo shi : Z),
    rw_cells asegs m (st + 192) [C8 (wz b); C8 (wz e); C8 (wz c)] -> SHAD m (st + 192) (repeat (b8 0) 3) -> st mod 8 = 0 ->
    aapp st ST_SIZE ->
    b <> 0 -> aapp b (c - b) -> b mod 16 = 0 -> b <= e <= c -> c - b <= 2 ^ 40 ->
    SHAD m b (cc_gen (c - b) (e - b)) -> (c <= st + 192 \/ st + 216 <= b) ->
    stack0 m lo shi -> spf <= shi ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (dv2_pre x24 x25 x26 x27 gp tp F fc st spf b c lo shi m)
      (MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 DV2) fc None m (seg_rom asegs)).
  Proof.
    intros until shi. intros CV SV V8 VA0 B0 BA B16 BE BL SB VBD S0 SHI ST CE LO SP16 SPR MI AC.
    eapply evt_cut; [eapply (dv2_a HANN); eassumption|].
    intros ms2 (w5 & w6 & w7 & d10 & d11 & d12 & d13 & d14 & d15 & d16 & d17 & w28 & w29 & w30 & w31 & m2 & EQ & MU & WM & MI2 & ST2
                & CV2 & SV2 & S02 & SH2 & AC2).
    subst ms2.
    eapply evt_mono; [eapply (dv2_b HANN); try eassumption; lia|].
    intros ms' (t5 & t6 & t7 & a2' & a3' & a4' & a5' & a6' & a7' & t28 & t29 & t30 & t31 & m' & EQ' & MU' & WM' & MI' & ST' & SH'
                & AC' & S0' & CV').
    exists t5, t6, t7, a2', a3', a4', a5', a6', a7', t28, t29, t30, t31, m'.
    split; [exact EQ'|].
    split.
    { eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU MU')].
      intros x Hx; cbn [app outside] in Hx |- *; clear - Hx; lia. }
    split; [exact (wmono_trans asegs _ _ _ WM WM')|].
    repeat (split; [assumption|]). assumption.
  Qed.

  Lemma dtv2 : forall (Q : config -> Prop)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (LF : list fframe)
      (st spf lo B shi : Z) (errv : word) (mo : Model) (pid : bptr) (b e c : Z),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                             (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DV2) fc None m (seg_rom asegs) ->
    rw_cells asegs m (st + 192) [C8 (wz b); C8 (wz e); C8 (wz c)] -> SHAD m (st + 192) (repeat (b8 0) 3) -> st mod 8 = 0 ->
    (b = 0 -> e = 0 /\ c = 0) ->
    (aapp st ST_SIZE \/ (spf <= st /\ st + ST_SIZE + 64 <= shi)) ->
    (b <> 0 -> In (pid, b, c - b) LB /\ b <= e <= c /\ c - b <= 2 ^ 40 /\ SHAD m b (cc_gen (c - b) (e - b))
               /\ (c <= st + 192 \/ st + 216 <= b) /\ st_live_frame LF st) ->
    lb_own LB m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m -> as_RFS H LF m -> stack0 m lo shi -> spf <= shi ->
    (b <> 0 -> trace_ok (as_TR H) APC0_FREE [DV2_N]) ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H)
            (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y23 y28 y29 y30 y31 : word),
       as_VIS H s' msF' = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                                 (Z_to_bv 64 0x7fff8000) y21 y22 y23 x24 x25 x26 x27 y28 y29 y30 y31)
                             F (Z_to_bv 64 DV2_N) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr tp) [C4 errv] -> as_rauxv_ok H m' B ->
       ACONST m' -> as_RFS H LF m' -> stack0 m' lo shi ->
       as_RHEAP H s' (dv_LB H LB pid b) m' -> lb_own (dv_LB H LB pid b) m' ->
       xpres H (dv_LB H LB pid b) spf [(st + 192, st + 216)] m m' -> as_AL H s' >= as_AL H s ->
       wr_at asegs m' (st + 192) 24 ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp
      F fc msF m s LB LF st spf lo B shi errv mo pid b e c VIS CV SV V8 B0E HLOC B1P OWN RH KR AL0 RA SPB ST CE LO ERR MI TP SP16 SPR
      AC RF S0 SHI TRC K.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK FR]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4). unfold AIMG_TOP in FS1.
    unfold AFREE_STACK, ST_SIZE in *.
    assert (STB : 0x6e6000 <= st /\ st + 240 <= 2 ^ 47).
    { destruct HLOC as [HA|[HS1 HS2]]; [pose proof (aapp_bounds st 240 HA ltac:(lia)) as (X1 & X2 & X3 & _); unfold AIMG_TOP, AAPP_HI in *; lia | lia]. }
    destruct (Z.eq_dec b 0) as [Bz | Bnz].
    -
      destruct (B0E Bz) as [E1 C1]. subst b e c.
      remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                 (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtV_2) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (GZV : gz m (st + 192) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DV2_N] (SCR [] [] []) DV2 (srs sr_id HTbAHStDtV_2)
         [ KWord (SA (EVar 32) 192) 8 (ELit 0);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DV2 m (seg_rom asegs) HR HK 200%nat [DV2_N] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      eapply (sr_blk H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1.
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 20%bv G20.
      rewrite HRe in VIS1. cbn [getr] in VIS1. rewrite ?G2, ?G8, ?G20 in VIS1.
      eapply K; [exact VIS1 | exact KR1 | exact MP1 | exact MI | exact ST | exact ERR | exact RA | exact AC | exact RF | exact S0
                | unfold dv_LB; rewrite Z.eqb_refl; exact RH | unfold dv_LB; rewrite Z.eqb_refl; exact OWN
                | apply xpres_refl | lia | exact (rw_cells_wr_at _ _ _ _ 24 CV ltac:(cbn; lia))].
    -
      destruct (B1P Bnz) as (INB & BE & BL & SB & BDV & (fv & INV & FV1 & FV2)). unfold ST_SIZE in FV1, FV2.
      pose proof (FR fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
      pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
      assert (VA0 : aapp st 240) by (eapply aapp_sub; [exact FS4 | unfold AFS_SIZE; lia | unfold AFS_SIZE; lia]).
      pose proof (aapp_bounds st 240 VA0 ltac:(lia)) as (SA1 & SA2 & SA3 & SA4 & SA5). unfold AIMG_TOP, AAPP_HI in SA1, SA3.
      pose proof (ah_blocks H HH _ _ _ _ RH INB) as ABR. unfold blk_addr, blk_size in ABR. cbn [fst snd] in ABR.
      pose proof ABR as (BB0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
      assert (SPH : sh b + nsh (c - b) <= 0x10007fff8000)
        by (pose proof (sh_nsh_high b (c - b) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
      assert (SHL : 0x7fff8000 <= sh b) by (unfold sh, ASHADOW_BASE; pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)); lia).
      assert (SPA : sh b + nsh (c - b) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).

      eapply (ahh_evt_then H HH (dv2_pre x24 x25 x26 x27 gp tp F fc st spf b c lo shi m)); [exact KR | exact VIS | |].
      { eapply dv2_pre_evt; try eassumption; unfold ST_SIZE, AFREE_STACK in *; lia. }
      intros msF1 mo1 KR1 MP1 (t5 & t6 & t7 & a2' & a3' & a4' & a5' & a6' & a7' & t28 & t29 & t30 & t31 & m1 & VIS1 & MU1 & WM1 & MI1
                                & ST1 & SH1 & AC1 & S01 & CV1).
      assert (W1 : Forall (fun iv : Z * Z => aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv)
                     [(st + 200, st + 208); (sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)]).
      { apply Forall_cons.
        { split; [right; right; right; right; left; cbn; unfold AFS_SIZE in *; lia|].
          split; [right; exists fv; split; [exact INV | cbn; lia]|].
          eapply (aconst_ok_app st 240); [exact VA0 | cbn; lia | cbn; lia]. }
        apply Forall_cons.
        { split; [right; right; right; left; exists (pid, b, c - b); split; [exact INB | cbn; lia]|].
          split.
          { left. cbn. pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE b (c - b) FS4 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S.
            unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. split; lia. }
          apply aconst_ok_high; [cbn [fst snd]; apply sh_mono; unfold AIMG_TOP; lia | right; left; cbn; lia]. }
        apply Forall_cons; [| apply Forall_nil].
        split; [left; cbn; unfold AINTRIN_STACK; lia|]. split; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AINTRIN_STACK in *; split; lia|].
        apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity; cbn; unfold AINTRIN_STACK; lia | right; left; cbn; unfold AINTRIN_STACK; lia]. }
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv) => proj1 K) W1) as W1C.
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv) => proj1 (proj2 K)) W1) as W1F.
      assert (RH1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W1C]).
      assert (RA1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | exact W1C]).
      assert (RF1 : as_RFS H LF m1) by (eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 | exact W1F]).
      assert (ERR1 : rw_cells asegs m1 (errno_addr tp) [C4 errv]).
      { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
        eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP, AINTRIN_STACK; lia]. }
      pose proof (lb_own_wmono _ _ _ OWN WM1) as OWN1.
      destruct (rw_cells_of_own LB m1 (pid, b, c - b) OWN1 INB ltac:(cbn; unfold AIMG_TOP; lia) ltac:(cbn; lia)) as (bs & CB1).
      cbn [blk_addr blk_size fst snd] in CB1.

      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (LB := LB) (p := pid) (A := b) (n := c - b) (lo := lo) (B := B) (errv := errv) (CH := [])
                                     (sbs := shadow_of (c - b)) (bs := bs);
          [exact VIS1 | exact RH1 | exact KR1 | exact INB | rewrite HCF; exact AL0 | exact CB1 | exact SH1 | rewrite shadow_of_length by lia; reflexivity
          | exact RA1 | rewrite u64_of_Z by lia; lia | rewrite u64_of_Z by lia; exact ST1
          | exact CE | rewrite u64_of_Z by lia; unfold AFREE_STACK; lia | exact ERR1 | exact MI1 | exact TP
          | rewrite u64_of_Z by lia; exact SP16 | exact AC1
          | rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; lia
          | rewrite u64_of_Z by (unfold DV2_N; lia); exact (TRC Bnz) | reflexivity ]. }
      intros [msF2 mo2] POST2.
      destruct POST2 as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & sA
                         & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & RH2 & AC2 & AL2).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite u64_of_Z in ST2, AP2 by lia.
      rewrite (ret_pc_even DV2_N ltac:(unfold DV2_N; lia) eq_refl) in VIS2.
      set (LB' := as_lb_remove H pid LB) in *.

      assert (FRM : forall a, 0 <= a < 2 ^ 64 -> (as_FSB H <= a < as_FSB H + AFS_SIZE \/ ATLS_PRIV_LO <= a < ATLS_PRIV_HI
                               \/ sh (as_FSB H) <= a < sh (as_FSB H + AFS_SIZE)) ->
                     m2 (wa a) = m1 (wa a) /\ (wview asegs m1 (wa a) <> None -> wview asegs m2 (wa a) <> None)).
      { intros a Ha Hr. apply (AP2 a Ha). unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
        - right; right; right; right; left; exact Hr.
        - right; left. unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. right; right; right; lia.
        - right; right; right; right; right; left; exact Hr. }
      assert (RF2 : as_RFS H LF m2) by (eapply (ah_RFS_ext H HH); [exact RF1 | exact FRM]).
      assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]).
      assert (OWN2 : lb_own LB' m2).
      { pose proof (ah_lb_remove H HH) as (_ & _ & L3).
        eapply (lb_own_apres H); [exact (lb_own_incl LB _ m1 (L3 pid LB) OWN1) | exact AP2 | intros bb Hb; exact Hb]. }
      assert (XP : xpres H LB' spf [(st + 192, st + 216)] m m2).
      { apply (xpres_drop_blk H HH s LB pid b (c - b) spf [(st + 192, st + 216)] m m m2 RH INB ltac:(lia)).
        eapply xpres_trans.
        { eapply (xpres_of_munch H sA LB' spf _ _ m2 m m1); [exact HH | exact RH2 | exact MU1 | exact WM1 |].
          apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia|].
          apply Forall_cons; [right; intros a Ha; cbn; right; right; left; cbn in Ha; lia|].
          apply Forall_cons; [left; cbn; unfold AINTRIN_STACK; lia | apply Forall_nil]. }
        exact (xpres_of_apres H _ _ _ _ _ AP2). }
      assert (WO : wr_at asegs m2 (st + 192) 24).
      { pose proof (wr_at_wmono _ _ _ _ (rw_cells_wr_at _ _ _ _ 24 CV ltac:(cbn; lia)) WM1) as (P0 & P1 & PW).
        split; [exact P0|]. split; [exact P1|]. intros i Hi.
        apply (proj2 (FRM (st + 192 + i) ltac:(lia) ltac:(left; unfold AFS_SIZE in *; lia))). apply PW. exact Hi. }
      eapply K; [exact VIS2 | exact KR2 | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2] | exact MI2 | exact ST2
                | exact ERR2 | exact RA2 | exact AC2 | exact RF2 | exact S02
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq b 0) Bnz); exact RH2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq b 0) Bnz); exact OWN2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq b 0) Bnz); exact XP
                | rewrite HCF in AL2; lia | exact WO].
  Qed.
End DtV2c.

Definition DV1 : Z := 0xeb110.  Definition DV1_A1 : Z := 0xeb168.  Definition DV1_A2 : Z := 0xeb198.  Definition DV1_N : Z := 0xeb1b8.

Section DtV1.
  Context {HCEIL : HeapCeil}.
  Hypothesis HANN : annotate_gen_stmt.

  Definition dv1_mid1 (x24 x25 x26 x27 gp tp : word) (F : bvmap 5 word) (fc : bv 32) (st spf b c lo shi : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists w5 w6 w7 d10 d11 d12 d13 d14 d15 d16 d17 w28 w29 w30 w31 m2,
      ms' = MS (mkR (Z_to_bv 64 DV1_A1) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 168))
                    d10 d11 d12 d13 d14 d15 d16 d17 (Z_to_bv 64 (st + 184)) (Z_to_bv 64 (st + 176)) (Z_to_bv 64 0x7fff8000)
                    (shw (st + 168)) (shw (st + 184)) (shw (st + 176)) x24 x25 x26 x27 w28 w29 w30 w31)
               F (Z_to_bv 64 DV1_A1) fc None m2 (seg_rom asegs)
      /\ munch [(st + 176, st + 184); (sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)] m m2
      /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo spf
      /\ rw_cells asegs m2 (st + 168) [C8 (wz b); C8 (wz b); C8 (wz c)]
      /\ SHAD m2 (st + 168) (repeat (b8 0) 3) /\ stack0 m2 lo shi /\ SHAD m2 b (cc_gen (c - b) 0) /\ ACONST m2.

  Lemma dv1_a : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (st spf b e c lo shi : Z),
    rw_cells asegs m (st + 168) [C8 (wz b); C8 (wz e); C8 (wz c)] -> SHAD m (st + 168) (repeat (b8 0) 3) -> st mod 8 = 0 ->
    aapp st ST_SIZE ->
    b <> 0 -> aapp b (c - b) -> b mod 16 = 0 -> b <= e <= c -> c - b <= 2 ^ 40 ->
    SHAD m b (cc_gen (c - b) (e - b)) -> (c <= st + 168 \/ st + 192 <= b) ->
    stack0 m lo shi -> spf <= shi ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (dv1_mid1 x24 x25 x26 x27 gp tp F fc st spf b c lo shi m)
      (MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 DV1) fc None m (seg_rom asegs)).
  Proof.
    intros until shi. intros CV SV V8 VA0 B0 BA B16 BE BL SB VBD S0 SHI ST CE LO SP16 SPR MI AC.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VA : aapp (st + 168) 24) by (eapply aapp_sub; [exact VA0 | lia | unfold ST_SIZE; lia]).
    pose proof (aapp_bounds st ST_SIZE VA0 ltac:(unfold ST_SIZE; lia)) as (SB1' & SB2' & SB3' & SB4' & SB5').
    unfold AFREE_STACK, ST_SIZE, AIMG_TOP in *.
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (aapp_bounds (st + 168) 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5).
    pose proof (aapp_bounds b (c - b) BA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
    unfold AIMG_TOP in VB1, PB1.
    remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 b; Z_to_bv 64 e; Z_to_bv 64 c]).
    assert (HR : regs_ok E (srs sr_id HTbAHStDtV_2) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (GZV : gz m (st + 168) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
    assert (HK : know_ok asegs E m
       (kn_fix 20 [AANNOTATE_CC] (SCR [] [] []) DV1 (srs sr_id HTbAHStDtV_2)
       [ KWord (SA (EVar 32) 168) 8 (EVar 34); KWord (SA (EVar 32) 176) 8 (EVar 35); KWord (SA (EVar 32) 184) 8 (EVar 36);
         KWr (SA (EVar 32) 168) (ELit 24);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47); KRange (EVar 34) 0x6e6000 (2 ^ 47) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV 8%nat (C8 (wz e)). }
      apply Forall_cons. { kword_cell CV 16%nat (C8 (wz c)). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact (proj2 CV) | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R DV1 m (seg_rom asegs) HR HK 200%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 SB0 SB1' SB2'.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: first [ sc_shdj | sc_dj ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rreg HR' 12%bv L12. rreg HR' 13%bv L13. rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23.
    rewrite ?w_add in L9, L18, L19, L21, L22, L23 by lia.

    assert (WV1 : forall a, st + 168 <= a -> a + 8 <= st + 192 -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (proj2 CV) as W. destruct W as (W1 & W2 & W). cbn [cells_size csize Z.of_nat] in W.
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (st + 168 + (a - (st + 168) + i)) by lia. apply W. cbn. lia. }
    assert (MU1 : munch [(st + 176, st + 184)] m M1).
    { subst M1. clear - Hlf VB1 VB2 VB3 SPR LO CE ACF1 ACF2. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spf) by (subst M1; apply stk_mem_denot; exact ST).
    assert (SVP : sh b + nsh (c - b) <= st + 168 \/ st + 192 <= sh b)
      by (pose proof (aapp_disjoint_sh (st + 168) 24 b (c - b) VA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)); lia).
    assert (SPH : sh b + nsh (c - b) <= 0x10007fff8000)
      by (pose proof (sh_nsh_high b (c - b) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
    assert (SPA : sh b + nsh (c - b) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHV : sh (st + 168) + 3 <= sh b \/ sh b + nsh (c - b) <= sh (st + 168)).
    { clear - VBD V8 B16 BE. unfold sh, nsh. Z.div_mod_to_equations. nia. }
    assert (SB1 : SHAD M1 b (cc_gen (c - b) (e - b))).
    { eapply SHAD_transport; [exact SB | exact MU1 | exact WM1 |]. rewrite cc_gen_length by lia. cbn. lia. }
    assert (SV1 : SHAD M1 (st + 168) (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV | exact MU1 | exact WM1 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      unfold sh, ASHADOW_BASE. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA. Z.div_mod_to_equations. lia. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [eapply (stack0_ok_aapp (st + 168) 24); [exact VA | cbn; lia | cbn; lia] | apply Forall_nil]. }
    assert (AC1 : ACONST M1).
    { eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |].
      apply Forall_cons; [eapply (aconst_ok_app (st + 168) 24); [exact VA | cbn; lia | cbn; lia] | apply Forall_nil]. }
    assert (CV1 : rw_cells asegs M1 (st + 168) [C8 (wz b); C8 (wz b); C8 (wz c)]).
    { change [C8 (wz b); C8 (wz e); C8 (wz c)] with ([C8 (wz b)] ++ [C8 (wz e)] ++ [C8 (wz c)]) in CV.
      apply rw_cells_app in CV as [CV0 CV']. apply rw_cells_app in CV' as [_ CV2].
      replace (st + 168 + Z.of_nat (cells_size [C8 (wz b)]) + Z.of_nat (cells_size [C8 (wz e)])) with (st + 184) in CV2 by (cbn; lia).
      apply rw_cells_cons8_c.
      { eapply rw_cells_transport; [exact CV0 | exact MU1 | exact WM1 | cbn; lia]. }
      apply rw_cells_cons8_c.
      { subst M1. clear - Hlf WV1 VB1 VB2 VB3 SPR LO CE ACF1 ACF2. replace (st + 168 + 8) with (st + 176) by lia.
        lgcell Hlf (WV1 (st + 176) ltac:(lia) ltac:(lia)) 0%nat. }
      replace (st + 168 + 8 + 8) with (st + 184) by lia.
      eapply rw_cells_transport; [exact CV2 | exact MU1 | exact WM1 | cbn; lia]. }

    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L8, L9, L10, L11, L12, L13, L18, L19, L20, L21, L22, L23.
    clear HRe HR' Hlf Hms HF1 L1 L2 L8 L9 L10 L11 L12 L13 L18 L19 L20 L21 L22 L23.
    eapply evt_cut.
    { eapply HANN with (beg := b) (len := c - b) (oldmid := e - b) (newmid := 0) (lo := lo); rewrite ?u64_of_Z by lia.
      - reflexivity.
      - f_equal; lia.
      - f_equal; lia.
      - rewrite Z.add_0_r. reflexivity.
      - Z.div_mod_to_equations; lia.
      - lia.
      - lia.
      - lia.
      - exact BA.
      - unfold AAPP_HI; lia.
      - exact SB1.
      - exact ST1.
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact MI1.
      - exact AC1.
      - eapply aapp_in_app_mem; [exact BA | lia | lia]. }
    intros ms2 POST2.
    destruct POST2 as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m2 & EQ2 & MU2 & WM2 & MI2 & ST2 & SH2 & AC2).
    subst ms2. rewrite u64_of_Z in MU2, ST2 by lia.
    rewrite (ret_pc_even 962920 ltac:(lia) eq_refl).
    assert (CV2 : rw_cells asegs m2 (st + 168) [C8 (wz b); C8 (wz b); C8 (wz c)])
      by (eapply rw_cells_transport; [exact CV1 | exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; lia]).
    assert (SV2 : SHAD m2 (st + 168) (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV1 | exact MU2 | exact WM2 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      assert (sh (st + 168) + 3 <= 0x10007fff8000) by (unfold sh, ASHADOW_BASE; unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA; Z.div_mod_to_equations; lia).
      unfold AINTRIN_STACK. lia. }
    assert (S02 : stack0 m2 lo shi).
    { eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 |].
      apply Forall_cons; [right; cbn; exact SPA|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO, AINTRIN_STACK; lia | apply Forall_nil]. }
    apply evt_done. exists w0, w1, w2, d0, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m2.
    split; [reflexivity|].
    split; [exact (munch_app _ _ _ _ _ MU1 MU2)|].
    split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact CV2|].
    split; [exact SV2|]. split; [exact S02|]. split; [exact SH2 | exact AC2].
  Qed.
End DtV1.

Section DtV1b.
  Context {HCEIL : HeapCeil}.
  Hypothesis HANN : annotate_gen_stmt.

  Definition dv1_del (x24 x25 x26 x27 gp tp : word) (F : bvmap 5 word) (fc : bv 32) (st spf b c lo shi : Z) (m2 : mem)
      : machine_state -> Prop :=
    fun ms' => exists w5 w6 w7 a2' a3' a4' a5' a6' a7' w28 w29 w30 w31 m',
      ms' = MS (mkR (Z_to_bv 64 DV1_N) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 168))
                    (Z_to_bv 64 b) (Z_to_bv 64 (c - b)) a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (st + 184)) (Z_to_bv 64 (st + 176)) (Z_to_bv 64 0x7fff8000)
                    (shw (st + 168)) (shw (st + 184)) (shw (st + 176)) x24 x25 x26 x27 w28 w29 w30 w31)
               F (Z_to_bv 64 AOPDEL2) fc None m' (seg_rom asegs)
      /\ munch [(sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)] m2 m'
      /\ wmono asegs m2 m' /\ mem_inv asegs m' /\ stk asegs m' lo spf
      /\ SHAD m' b (shadow_of (c - b)) /\ ACONST m' /\ stack0 m' lo shi
      /\ rw_cells asegs m' (st + 168) [C8 (wz b); C8 (wz b); C8 (wz c)].

#[local] Definition HTbAHStDtV_4 : list (reg * expr) := [(2%bv, EVar 33); (8%bv, EVar 32); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 168)); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 184)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 176)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 168)) (ELit 3)) (ELit 2147450880)); (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 184)) (ELit 3)) (ELit 2147450880)); (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 176)) (ELit 3)) (ELit 2147450880))].
  Lemma dv1_b : forall (w5 w6 w7 d10 d11 d12 d13 d14 d15 d16 d17 x24 x25 x26 x27 w28 w29 w30 w31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (m2 : mem) (st spf b c lo shi : Z),
    stk asegs m2 lo spf -> mem_inv asegs m2 ->
    rw_cells asegs m2 (st + 168) [C8 (wz b); C8 (wz b); C8 (wz c)] ->
    SHAD m2 (st + 168) (repeat (b8 0) 3) -> stack0 m2 lo shi -> SHAD m2 b (cc_gen (c - b) 0) -> ACONST m2 ->
    st mod 8 = 0 -> aapp st ST_SIZE ->
    b <> 0 -> aapp b (c - b) -> b mod 16 = 0 -> b <= c -> c - b <= 2 ^ 40 -> (c <= st + 168 \/ st + 192 <= b) ->
    spf <= shi ->
    aceil <= lo -> lo <= spf - AFREE_STACK -> spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 ->
    evt asegs (dv1_del x24 x25 x26 x27 gp tp F fc st spf b c lo shi m2)
      (MS (mkR (Z_to_bv 64 DV1_A1) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 168))
               d10 d11 d12 d13 d14 d15 d16 d17 (Z_to_bv 64 (st + 184)) (Z_to_bv 64 (st + 176)) (Z_to_bv 64 0x7fff8000)
               (shw (st + 168)) (shw (st + 184)) (shw (st + 176)) x24 x25 x26 x27 w28 w29 w30 w31)
          F (Z_to_bv 64 DV1_A1) fc None m2 (seg_rom asegs)).
  Proof.
    intros until shi. intros ST2 MI2 CV2 SV2 S02 SH2 AC2 V8 VA0 B0 BA B16 BE BL VBD SHI CE LO SP16 SPR.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VA : aapp (st + 168) 24) by (eapply aapp_sub; [exact VA0 | lia | unfold ST_SIZE; lia]).
    pose proof (aapp_bounds st ST_SIZE VA0 ltac:(unfold ST_SIZE; lia)) as (SB1' & SB2' & SB3' & SB4' & SB5').
    unfold AFREE_STACK, ST_SIZE, AIMG_TOP in *.
    pose proof (stack0_bounds m2 lo shi S02) as SB0. unfold AAPP_HI in SB0.
    pose proof (aapp_bounds (st + 168) 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5).
    pose proof (aapp_bounds b (c - b) BA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
    unfold AIMG_TOP in VB1, PB1.
    assert (SVP : sh b + nsh (c - b) <= st + 168 \/ st + 192 <= sh b)
      by (pose proof (aapp_disjoint_sh (st + 168) 24 b (c - b) VA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)); lia).
    assert (SPH : sh b + nsh (c - b) <= 0x10007fff8000)
      by (pose proof (sh_nsh_high b (c - b) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
    assert (SPA : sh b + nsh (c - b) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).

    lazymatch goal with |- evt _ _ (MS ?T _ _ _ _ _ _) => remember T as R2 eqn:HR2 end.
    pose (E2 := Eseed R2 [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 b; Z_to_bv 64 c]).
    assert (HR2s : regs_ok E2 (srs sr_id HTbAHStDtV_4) R2).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R2; evs; try reflexivity;
        unfold shw; rewrite ?w_addm, ?w_add by lia; reflexivity. }
    assert (GZV2 : gz m2 (st + 168) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV2 | cbn; lia]).
    assert (HK2 : know_ok asegs E2 m2
       (kn_fix 20 [AANNOTATE_CC] (SCR [] [] []) DV1_A1
          (srs sr_id HTbAHStDtV_4)
       [ KWord (SA (EVar 32) 168) 8 (EVar 34); KWord (SA (EVar 32) 176) 8 (EVar 34); KWord (SA (EVar 32) 184) 8 (EVar 35);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47); KRange (EVar 34) 0x6e6000 (2 ^ 47) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CV2 0%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV2 8%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV2 16%nat (C8 (wz c)). }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R2 DV1_A1 m2 (seg_rom asegs) HR2s HK2 200%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E2 VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 SB0 SB1' SB2'.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: first [ sc_shdj | sc_dj ]. }
    clear HK2.
    assert (HF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF2) as HF2'. cbn [ms_regs] in HF2'.
    readback HR' HF2' HR2 HRe2.
    rreg HR' 1%bv K1. rreg HR' 10%bv K10. rreg HR' 11%bv K11. rreg HR' 12%bv K12. rreg HR' 13%bv K13.
    rreg HR' 2%bv K2. rreg HR' 8%bv K8. rreg HR' 9%bv K9. rreg HR' 18%bv K18. rreg HR' 19%bv K19. rreg HR' 20%bv K20.
    rreg HR' 21%bv K21. rreg HR' 22%bv K22. rreg HR' 23%bv K23.
    rewrite ?w_add in K9, K18, K19, K21, K22, K23 by lia.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe2, K1, K10, K11, K12, K13, K2, K8, K9, K18, K19, K20, K21, K22, K23.
    clear HRe2 HR' Hlf Hms HF2' K1 K10 K11 K12 K13 K2 K8 K9 K18 K19 K20 K21 K22 K23.

    eapply evt_cut.
    { eapply HANN with (beg := b) (len := c - b) (oldmid := 0) (newmid := c - b) (lo := lo); rewrite ?u64_of_Z by lia.
      - reflexivity.
      - f_equal; lia.
      - rewrite Z.add_0_r. reflexivity.
      - f_equal; lia.
      - Z.div_mod_to_equations; lia.
      - lia.
      - lia.
      - lia.
      - exact BA.
      - unfold AAPP_HI; lia.
      - exact SH2.
      - exact ST2.
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact MI2.
      - exact AC2.
      - eapply aapp_in_app_mem; [exact BA | lia | lia]. }
    intros ms4 POST4.
    destruct POST4 as (v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m4 & EQ4 & MU4 & WM4 & MI4 & ST4 & SH4 & AC4).
    subst ms4. rewrite u64_of_Z in MU4, ST4 by lia.
    rewrite (ret_pc_even 962968 ltac:(lia) eq_refl).
    rewrite cc_gen_full in SH4.

    assert (CV4 : rw_cells asegs m4 (st + 168) [C8 (wz b); C8 (wz b); C8 (wz c)])
      by (eapply rw_cells_transport; [exact CV2 | exact MU4 | exact WM4 | cbn; unfold AINTRIN_STACK; lia]).
    assert (SV4 : SHAD m4 (st + 168) (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV2 | exact MU4 | exact WM4 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      assert (sh (st + 168) + 3 <= 0x10007fff8000) by (unfold sh, ASHADOW_BASE; unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA; Z.div_mod_to_equations; lia).
      assert (SHV : sh (st + 168) + 3 <= sh b \/ sh b + nsh (c - b) <= sh (st + 168)).
      { clear - VBD V8 B16 BE. unfold sh, nsh. Z.div_mod_to_equations. nia. }
      unfold AINTRIN_STACK. lia. }
    assert (S04 : stack0 m4 lo shi).
    { eapply stack0_transport; [exact S02 | exact MU4 | exact WM4 |].
      apply Forall_cons; [right; cbn; exact SPA|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO, AINTRIN_STACK; lia | apply Forall_nil]. }

    lazymatch goal with |- evt _ _ (MS ?T _ _ _ _ _ _) => remember T as R3 eqn:HR3 end.
    pose (E3 := Eseed R3 [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 b; Z_to_bv 64 c]).
    assert (HR3s : regs_ok E3 (srs sr_id HTbAHStDtV_4) R3).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R3; evs; try reflexivity;
        unfold shw; rewrite ?w_addm, ?w_add by lia; reflexivity. }
    assert (GZV4 : gz m4 (st + 168) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV4 | cbn; lia]).
    assert (HK3 : know_ok asegs E3 m4
       (kn_fix 20 [AOPDEL2] (SCR [] [] []) DV1_A2
          (srs sr_id HTbAHStDtV_4)
       [ KWord (SA (EVar 32) 168) 8 (EVar 34); KWord (SA (EVar 32) 184) 8 (EVar 35);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47); KRange (EVar 34) 0x6e6000 (2 ^ 47) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CV4 0%nat (C8 (wz b)). }
      apply Forall_cons. { kword_cell CV4 16%nat (C8 (wz c)). }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R3 DV1_A2 m4 (seg_rom asegs) HR3s HK3 200%nat [AOPDEL2] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E3 VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 SB0 SB1' SB2'.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: first [ sc_shdj | sc_dj ]. }
    clear HK3.
    assert (HF3 : rfull R3) by (rewrite HR3; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF3) as HF3'. cbn [ms_regs] in HF3'.
    readback HR' HF3' HR3 HRe3.
    rreg HR' 1%bv J1. rreg HR' 10%bv J10. rreg HR' 11%bv J11.
    rreg HR' 2%bv J2. rreg HR' 8%bv J8. rreg HR' 9%bv J9. rreg HR' 18%bv J18. rreg HR' 19%bv J19. rreg HR' 20%bv J20.
    rreg HR' 21%bv J21. rreg HR' 22%bv J22. rreg HR' 23%bv J23.
    rewrite ?w_add in J9, J18, J19, J21, J22, J23 by lia. rewrite w_negadd in J11 by lia.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe3, J1, J10, J11, J2, J8, J9, J18, J19, J20, J21, J22, J23.
    apply evt_done.
    do 14 eexists. split; [reflexivity|].
    split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|]. split; [exact ST4|].
    split; [exact SH4|]. split; [exact AC4|]. split; [exact S04 | exact CV4].
  Qed.
End DtV1b.

Section DtV1c.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HANN : annotate_gen_stmt.
  Hypothesis HCF : forall n, as_Cf H n = 0.

  Definition dv1_pre (x24 x25 x26 x27 gp tp : word) (F : bvmap 5 word) (fc : bv 32) (st spf b c lo shi : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists w5 w6 w7 a2' a3' a4' a5' a6' a7' w28 w29 w30 w31 m1,
      ms' = MS (mkR (Z_to_bv 64 DV1_N) (Z_to_bv 64 spf) gp tp w5 w6 w7 (Z_to_bv 64 st) (Z_to_bv 64 (st + 168))
                    (Z_to_bv 64 b) (Z_to_bv 64 (c - b)) a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (st + 184)) (Z_to_bv 64 (st + 176)) (Z_to_bv 64 0x7fff8000)
                    (shw (st + 168)) (shw (st + 184)) (shw (st + 176)) x24 x25 x26 x27 w28 w29 w30 w31)
               F (Z_to_bv 64 AOPDEL2) fc None m1 (seg_rom asegs)
      /\ munch [(st + 176, st + 184); (sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)] m m1
      /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo spf
      /\ SHAD m1 b (shadow_of (c - b)) /\ ACONST m1 /\ stack0 m1 lo shi
      /\ rw_cells asegs m1 (st + 168) [C8 (wz b); C8 (wz b); C8 (wz c)].

  Lemma dv1_pre_evt : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (st spf b e c lo shi : Z),
    rw_cells asegs m (st + 168) [C8 (wz b); C8 (wz e); C8 (wz c)] -> SHAD m (st + 168) (repeat (b8 0) 3) -> st mod 8 = 0 ->
    aapp st ST_SIZE ->
    b <> 0 -> aapp b (c - b) -> b mod 16 = 0 -> b <= e <= c -> c - b <= 2 ^ 40 ->
    SHAD m b (cc_gen (c - b) (e - b)) -> (c <= st + 168 \/ st + 192 <= b) ->
    stack0 m lo shi -> spf <= shi ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (dv1_pre x24 x25 x26 x27 gp tp F fc st spf b c lo shi m)
      (MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 DV1) fc None m (seg_rom asegs)).
  Proof.
    intros until shi. intros CV SV V8 VA0 B0 BA B16 BE BL SB VBD S0 SHI ST CE LO SP16 SPR MI AC.
    eapply evt_cut; [eapply (dv1_a HANN); eassumption|].
    intros ms2 (w5 & w6 & w7 & d10 & d11 & d12 & d13 & d14 & d15 & d16 & d17 & w28 & w29 & w30 & w31 & m2 & EQ & MU & WM & MI2 & ST2
                & CV2 & SV2 & S02 & SH2 & AC2).
    subst ms2.
    eapply evt_mono; [eapply (dv1_b HANN); try eassumption; lia|].
    intros ms' (t5 & t6 & t7 & a2' & a3' & a4' & a5' & a6' & a7' & t28 & t29 & t30 & t31 & m' & EQ' & MU' & WM' & MI' & ST' & SH'
                & AC' & S0' & CV').
    exists t5, t6, t7, a2', a3', a4', a5', a6', a7', t28, t29, t30, t31, m'.
    split; [exact EQ'|].
    split.
    { eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU MU')].
      intros x Hx; cbn [app outside] in Hx |- *; clear - Hx; lia. }
    split; [exact (wmono_trans asegs _ _ _ WM WM')|].
    repeat (split; [assumption|]). assumption.
  Qed.

  Lemma dtv1 : forall (Q : config -> Prop)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (LF : list fframe)
      (st spf lo B shi : Z) (errv : word) (mo : Model) (pid : bptr) (b e c : Z),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                             (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DV1) fc None m (seg_rom asegs) ->
    rw_cells asegs m (st + 168) [C8 (wz b); C8 (wz e); C8 (wz c)] -> SHAD m (st + 168) (repeat (b8 0) 3) -> st mod 8 = 0 ->
    (b = 0 -> e = 0 /\ c = 0) ->
    (aapp st ST_SIZE \/ (spf <= st /\ st + ST_SIZE + 64 <= shi)) ->
    (b <> 0 -> In (pid, b, c - b) LB /\ b <= e <= c /\ c - b <= 2 ^ 40 /\ SHAD m b (cc_gen (c - b) (e - b))
               /\ (c <= st + 168 \/ st + 192 <= b) /\ st_live_frame LF st) ->
    lb_own LB m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m -> as_RFS H LF m -> stack0 m lo shi -> spf <= shi ->
    (b <> 0 -> trace_ok (as_TR H) APC0_FREE [DV1_N]) ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H)
            (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y23 y28 y29 y30 y31 : word),
       as_VIS H s' msF' = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                                 (Z_to_bv 64 0x7fff8000) y21 y22 y23 x24 x25 x26 x27 y28 y29 y30 y31)
                             F (Z_to_bv 64 DV1_N) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr tp) [C4 errv] -> as_rauxv_ok H m' B ->
       ACONST m' -> as_RFS H LF m' -> stack0 m' lo shi ->
       as_RHEAP H s' (dv_LB H LB pid b) m' -> lb_own (dv_LB H LB pid b) m' ->
       xpres H (dv_LB H LB pid b) spf [(st + 168, st + 192)] m m' -> as_AL H s' >= as_AL H s ->
       wr_at asegs m' (st + 168) 24 ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp
      F fc msF m s LB LF st spf lo B shi errv mo pid b e c VIS CV SV V8 B0E HLOC B1P OWN RH KR AL0 RA SPB ST CE LO ERR MI TP SP16 SPR
      AC RF S0 SHI TRC K.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK FR]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4). unfold AIMG_TOP in FS1.
    unfold AFREE_STACK, ST_SIZE in *.
    assert (STB : 0x6e6000 <= st /\ st + 240 <= 2 ^ 47).
    { destruct HLOC as [HA|[HS1 HS2]]; [pose proof (aapp_bounds st 240 HA ltac:(lia)) as (X1 & X2 & X3 & _); unfold AIMG_TOP, AAPP_HI in *; lia | lia]. }
    destruct (Z.eq_dec b 0) as [Bz | Bnz].
    -
      destruct (B0E Bz) as [E1 C1]. subst b e c.
      remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                 (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtV_2) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (GZV : gz m (st + 168) 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DV1_N] (SCR [] [] []) DV1 (srs sr_id HTbAHStDtV_2)
         [ KWord (SA (EVar 32) 168) 8 (ELit 0);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DV1 m (seg_rom asegs) HR HK 200%nat [DV1_N] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      eapply (sr_blk H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1.
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 20%bv G20.
      rewrite HRe in VIS1. cbn [getr] in VIS1. rewrite ?G2, ?G8, ?G20 in VIS1.
      eapply K; [exact VIS1 | exact KR1 | exact MP1 | exact MI | exact ST | exact ERR | exact RA | exact AC | exact RF | exact S0
                | unfold dv_LB; rewrite Z.eqb_refl; exact RH | unfold dv_LB; rewrite Z.eqb_refl; exact OWN
                | apply xpres_refl | lia | exact (rw_cells_wr_at _ _ _ _ 24 CV ltac:(cbn; lia))].
    -
      destruct (B1P Bnz) as (INB & BE & BL & SB & BDV & (fv & INV & FV1 & FV2)). unfold ST_SIZE in FV1, FV2.
      pose proof (FR fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
      pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
      assert (VA0 : aapp st 240) by (eapply aapp_sub; [exact FS4 | unfold AFS_SIZE; lia | unfold AFS_SIZE; lia]).
      pose proof (aapp_bounds st 240 VA0 ltac:(lia)) as (SA1 & SA2 & SA3 & SA4 & SA5). unfold AIMG_TOP, AAPP_HI in SA1, SA3.
      pose proof (ah_blocks H HH _ _ _ _ RH INB) as ABR. unfold blk_addr, blk_size in ABR. cbn [fst snd] in ABR.
      pose proof ABR as (BB0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
      assert (SPH : sh b + nsh (c - b) <= 0x10007fff8000)
        by (pose proof (sh_nsh_high b (c - b) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
      assert (SHL : 0x7fff8000 <= sh b) by (unfold sh, ASHADOW_BASE; pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)); lia).
      assert (SPA : sh b + nsh (c - b) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).

      eapply (ahh_evt_then H HH (dv1_pre x24 x25 x26 x27 gp tp F fc st spf b c lo shi m)); [exact KR | exact VIS | |].
      { eapply dv1_pre_evt; try eassumption; unfold ST_SIZE, AFREE_STACK in *; lia. }
      intros msF1 mo1 KR1 MP1 (t5 & t6 & t7 & a2' & a3' & a4' & a5' & a6' & a7' & t28 & t29 & t30 & t31 & m1 & VIS1 & MU1 & WM1 & MI1
                                & ST1 & SH1 & AC1 & S01 & CV1).
      assert (W1 : Forall (fun iv : Z * Z => aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv)
                     [(st + 176, st + 184); (sh b, sh b + nsh (c - b)); (spf - AINTRIN_STACK, spf)]).
      { apply Forall_cons.
        { split; [right; right; right; right; left; cbn; unfold AFS_SIZE in *; lia|].
          split; [right; exists fv; split; [exact INV | cbn; lia]|].
          eapply (aconst_ok_app st 240); [exact VA0 | cbn; lia | cbn; lia]. }
        apply Forall_cons.
        { split; [right; right; right; left; exists (pid, b, c - b); split; [exact INB | cbn; lia]|].
          split.
          { left. cbn. pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE b (c - b) FS4 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S.
            unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. split; lia. }
          apply aconst_ok_high; [cbn [fst snd]; apply sh_mono; unfold AIMG_TOP; lia | right; left; cbn; lia]. }
        apply Forall_cons; [| apply Forall_nil].
        split; [left; cbn; unfold AINTRIN_STACK; lia|]. split; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AINTRIN_STACK in *; split; lia|].
        apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity; cbn; unfold AINTRIN_STACK; lia | right; left; cbn; unfold AINTRIN_STACK; lia]. }
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv) => proj1 K) W1) as W1C.
      pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv) => proj1 (proj2 K)) W1) as W1F.
      assert (RH1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W1C]).
      assert (RA1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | exact W1C]).
      assert (RF1 : as_RFS H LF m1) by (eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 | exact W1F]).
      assert (ERR1 : rw_cells asegs m1 (errno_addr tp) [C4 errv]).
      { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
        eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP, AINTRIN_STACK; lia]. }
      pose proof (lb_own_wmono _ _ _ OWN WM1) as OWN1.
      destruct (rw_cells_of_own LB m1 (pid, b, c - b) OWN1 INB ltac:(cbn; unfold AIMG_TOP; lia) ltac:(cbn; lia)) as (bs & CB1).
      cbn [blk_addr blk_size fst snd] in CB1.

      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (LB := LB) (p := pid) (A := b) (n := c - b) (lo := lo) (B := B) (errv := errv) (CH := [])
                                     (sbs := shadow_of (c - b)) (bs := bs);
          [exact VIS1 | exact RH1 | exact KR1 | exact INB | rewrite HCF; exact AL0 | exact CB1 | exact SH1 | rewrite shadow_of_length by lia; reflexivity
          | exact RA1 | rewrite u64_of_Z by lia; lia | rewrite u64_of_Z by lia; exact ST1
          | exact CE | rewrite u64_of_Z by lia; unfold AFREE_STACK; lia | exact ERR1 | exact MI1 | exact TP
          | rewrite u64_of_Z by lia; exact SP16 | exact AC1
          | rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; lia
          | rewrite u64_of_Z by (unfold DV1_N; lia); exact (TRC Bnz) | reflexivity ]. }
      intros [msF2 mo2] POST2.
      destruct POST2 as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & sA
                         & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & RH2 & AC2 & AL2).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite u64_of_Z in ST2, AP2 by lia.
      rewrite (ret_pc_even DV1_N ltac:(unfold DV1_N; lia) eq_refl) in VIS2.
      set (LB' := as_lb_remove H pid LB) in *.

      assert (FRM : forall a, 0 <= a < 2 ^ 64 -> (as_FSB H <= a < as_FSB H + AFS_SIZE \/ ATLS_PRIV_LO <= a < ATLS_PRIV_HI
                               \/ sh (as_FSB H) <= a < sh (as_FSB H + AFS_SIZE)) ->
                     m2 (wa a) = m1 (wa a) /\ (wview asegs m1 (wa a) <> None -> wview asegs m2 (wa a) <> None)).
      { intros a Ha Hr. apply (AP2 a Ha). unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
        - right; right; right; right; left; exact Hr.
        - right; left. unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. right; right; right; lia.
        - right; right; right; right; right; left; exact Hr. }
      assert (RF2 : as_RFS H LF m2) by (eapply (ah_RFS_ext H HH); [exact RF1 | exact FRM]).
      assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]).
      assert (OWN2 : lb_own LB' m2).
      { pose proof (ah_lb_remove H HH) as (_ & _ & L3).
        eapply (lb_own_apres H); [exact (lb_own_incl LB _ m1 (L3 pid LB) OWN1) | exact AP2 | intros bb Hb; exact Hb]. }
      assert (XP : xpres H LB' spf [(st + 168, st + 192)] m m2).
      { apply (xpres_drop_blk H HH s LB pid b (c - b) spf [(st + 168, st + 192)] m m m2 RH INB ltac:(lia)).
        eapply xpres_trans.
        { eapply (xpres_of_munch H sA LB' spf _ _ m2 m m1); [exact HH | exact RH2 | exact MU1 | exact WM1 |].
          apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia|].
          apply Forall_cons; [right; intros a Ha; cbn; right; right; left; cbn in Ha; lia|].
          apply Forall_cons; [left; cbn; unfold AINTRIN_STACK; lia | apply Forall_nil]. }
        exact (xpres_of_apres H _ _ _ _ _ AP2). }
      assert (WO : wr_at asegs m2 (st + 168) 24).
      { pose proof (wr_at_wmono _ _ _ _ (rw_cells_wr_at _ _ _ _ 24 CV ltac:(cbn; lia)) WM1) as (P0 & P1 & PW).
        split; [exact P0|]. split; [exact P1|]. intros i Hi.
        apply (proj2 (FRM (st + 168 + i) ltac:(lia) ltac:(left; unfold AFS_SIZE in *; lia))). apply PW. exact Hi. }
      eapply K; [exact VIS2 | exact KR2 | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2] | exact MI2 | exact ST2
                | exact ERR2 | exact RA2 | exact AC2 | exact RF2 | exact S02
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq b 0) Bnz); exact RH2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq b 0) Bnz); exact OWN2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq b 0) Bnz); exact XP
                | rewrite HCF in AL2; lia | exact WO].
  Qed.
End DtV1c.

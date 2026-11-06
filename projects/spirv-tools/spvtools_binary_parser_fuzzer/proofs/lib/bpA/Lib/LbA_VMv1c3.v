(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0 AsWalk CXXRep RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_VecT LbA_VecD1 LbA_VMvStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition VM1_A1_RET_c3 : Z := 0xf4b80.

Section VMv1.
  Context {HCEIL : HeapCeil}.
  Hypothesis HANN : annotate_gen_stmt.

  Definition vm_mid1_c3 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (v w b1 c1 lo shi : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 m2,
      ms' = MS (mkR (Z_to_bv 64 VM1_A1_RET_c3) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp w0 w1 w2 (Z_to_bv 64 v) (Z_to_bv 64 w)
                    d0 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 (v + 16)) (Z_to_bv 64 (v + 8)) (Z_to_bv 64 0x7fff8000)
                    (shw v) (shw (v + 16)) (shw (v + 8)) s8 s9 s10 s11 w3 w4 w5 w6)
               F (Z_to_bv 64 VM1_A1_RET_c3) fc None m2 (seg_rom asegs)
      /\ munch [(v + 8, v + 16); (bv_unsigned sp - 80, bv_unsigned sp); (sh b1, sh b1 + nsh (c1 - b1));
                (bv_unsigned sp - 80 - 4096, bv_unsigned sp - 80)] m m2
      /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (bv_unsigned sp)
      /\ rw_cells asegs m2 v [C8 (wz b1); C8 (wz b1); C8 (wz c1)]
      /\ rw_cells asegs m2 (bv_unsigned sp - 72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ SHAD m2 v (repeat (b8 0) 3) /\ stack0 m2 lo shi /\ SHAD m2 b1 (cc_gen (c1 - b1) 0) /\ ACONST m2.

  Lemma vm_a_c3 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (v w b1 e1 c1 lo shi : Z),
    a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 w ->
    rw_cells asegs m v [C8 (wz b1); C8 (wz e1); C8 (wz c1)] -> SHAD m v (repeat (b8 0) 3) -> v mod 8 = 0 ->
    aapp v 24 -> v + 24 <= bv_unsigned sp - AVMOVE_STACK ->
    b1 <> 0 -> aapp b1 (c1 - b1) -> b1 mod 16 = 0 -> b1 <= e1 <= c1 -> c1 - b1 <= 2 ^ 40 ->
    SHAD m b1 (cc_gen (c1 - b1) (e1 - b1)) -> (c1 <= v \/ v + 24 <= b1) ->
    stack0 m lo shi -> bv_unsigned sp <= shi ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AVMOVE_STACK ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (vm_mid1_c3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v w b1 c1 lo shi m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVMOVE_3) fc None m (seg_rom asegs)).
  Proof.
    intros until shi. intros Ha0 Ha1 CV SV V8 VA VAP B0 BA B16 BE BL SB VBD S0 SHI ST CE LO SP16 SPR MI AC.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    unfold AVMOVE_STACK, AFREE_STACK in LO, VAP.
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (aapp_bounds v 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5).
    pose proof (aapp_bounds b1 (c1 - b1) BA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
    unfold AIMG_TOP in VB1, PB1.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.

    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 spz; Z_to_bv 64 w; Z_to_bv 64 b1; Z_to_bv 64 e1; Z_to_bv 64 c1]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (11%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; [exact Ha0 | exact Hsp | exact Ha1]. }
    pose proof (ACONST_shbase m AC) as [CG CS].
    assert (GZV : gz m v 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
    assert (HK : know_ok asegs E m
       (kn_fix 20 [AANNOTATE_CC] (SCR [] [] []) AVMOVE_3 (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (11%bv, EVar 34)])
       [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
         KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
         KWord (SA (EVar 32) 0) 8 (EVar 35); KWord (SA (EVar 32) 8) 8 (EVar 36); KWord (SA (EVar 32) 16) 8 (EVar 37);
         KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EVar 33) (-80)) (ELit 80);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47); KRange (EVar 35) 0x6e6000 (2 ^ 47);
         KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-80)) (ELit 80) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1836e0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x18f6f8 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz b1)). }
      apply Forall_cons. { kword_cell CV 8%nat (C8 (wz e1)). }
      apply Forall_cons. { kword_cell CV 16%nat (C8 (wz c1)). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact (proj2 CV) | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia|].
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R AVMOVE_3 m (seg_rom asegs) HR HK 200%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 SB0 VAP.
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
    rewrite w_addm in L2 by lia. rewrite w_add in L18, L19, L22, L23 by lia.

    assert (WS1 : forall a, spz - 80 <= a -> a + 8 <= spz -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (wr_at_of_stk asegs m lo spz ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (WV1 : forall a, v <= a -> a + 8 <= v + 24 -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (proj2 CV) as W. destruct W as (W1 & W2 & W). cbn [cells_size csize Z.of_nat] in W.
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (v + (a - v + i)) by lia. apply W. cbn. lia. }
    assert (MU1 : munch [(v + 8, v + 16); (spz - 80, spz)] m M1).
    { subst M1. clear - Hlf VAP SPR LO CE ACF1 ACF2 VB1 VB2 VB3. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (SVP : sh b1 + nsh (c1 - b1) <= v \/ v + 24 <= sh b1)
      by (apply (aapp_disjoint_sh v 24 b1 (c1 - b1) VA); unfold AAPP_HI; lia).
    assert (SPH : sh b1 + nsh (c1 - b1) <= 0x10007fff8000)
      by (pose proof (sh_nsh_high b1 (c1 - b1) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
    assert (SPA : sh b1 + nsh (c1 - b1) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHV : sh v + 3 <= sh b1 \/ sh b1 + nsh (c1 - b1) <= sh v).
    { clear - VBD V8 B16 BE. unfold sh, nsh. Z.div_mod_to_equations. nia. }
    assert (SB1 : SHAD M1 b1 (cc_gen (c1 - b1) (e1 - b1))).
    { eapply SHAD_transport; [exact SB | exact MU1 | exact WM1 |]. rewrite cc_gen_length by lia. cbn. lia. }
    assert (SV1 : SHAD M1 v (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV | exact MU1 | exact WM1 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      unfold sh, ASHADOW_BASE. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA. Z.div_mod_to_equations. lia. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [eapply (stack0_ok_aapp v 24); [exact VA | lia | lia]|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (AC1 : ACONST M1).
    { eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |].
      apply Forall_cons; [eapply (aconst_ok_app v 24); [exact VA | cbn; lia | cbn; lia]|].
      apply Forall_cons; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity; cbn; lia | right; left; cbn; lia] | apply Forall_nil]. }
    assert (CV1 : rw_cells asegs M1 v [C8 (wz b1); C8 (wz b1); C8 (wz c1)]).
    { change [C8 (wz b1); C8 (wz e1); C8 (wz c1)] with ([C8 (wz b1)] ++ [C8 (wz e1)] ++ [C8 (wz c1)]) in CV.
      apply rw_cells_app in CV as [CV0 CV']. apply rw_cells_app in CV' as [_ CV2].
      replace (v + Z.of_nat (cells_size [C8 (wz b1)]) + Z.of_nat (cells_size [C8 (wz e1)])) with (v + 16) in CV2 by (cbn; lia).
      apply rw_cells_cons8_c.
      { eapply rw_cells_transport; [exact CV0 | exact MU1 | exact WM1 | cbn; lia]. }
      apply rw_cells_cons8_c.
      { subst M1. clear - Hlf WV1 VAP SPR LO CE ACF1 ACF2 VB1 VB2 VB3. lgcell Hlf (WV1 (v + 8) ltac:(lia) ltac:(lia)) 0%nat. }
      replace (v + 8 + 8) with (v + 16) by lia.
      eapply rw_cells_transport; [exact CV2 | exact MU1 | exact WM1 | cbn; lia]. }
    assert (CF1 : rw_cells asegs M1 (spz - 72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { subst M1. clear - Hlf WS1 VAP SPR LO CE ACF1 ACF2 VB1 VB2 VB3 HR0.
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72) ltac:(lia) ltac:(lia)) 1%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8) ltac:(lia) ltac:(lia)) 2%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8) ltac:(lia) ltac:(lia)) 3%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 4%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 5%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 6%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 7%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 8%nat|].
      lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 9%nat. }

    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L8, L9, L10, L11, L12, L13, L18, L19, L20, L21, L22, L23.
    clear HRe HR' Hlf Hms HF1 L1 L2 L8 L9 L10 L11 L12 L13 L18 L19 L20 L21 L22 L23.
    eapply evt_cut.
    { eapply HANN with (beg := b1) (len := c1 - b1) (oldmid := e1 - b1) (newmid := 0) (lo := lo); rewrite ?u64_of_Z by lia.
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
      - exact (proj1 (stk_split asegs M1 lo (spz - 80) spz ST1 ltac:(lia))).
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact MI1.
      - exact AC1.
      - eapply aapp_in_app_mem; [exact BA | lia | lia]. }
    intros ms2 POST2.
    destruct POST2 as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m2 & EQ2 & MU2 & WM2 & MI2 & ST2 & SH2 & AC2).
    subst ms2. rewrite u64_of_Z in MU2, ST2 by lia. unfold AINTRIN_STACK in MU2.
    rewrite (ret_pc_even 1002368 ltac:(lia) eq_refl).

    assert (CV2 : rw_cells asegs m2 v [C8 (wz b1); C8 (wz b1); C8 (wz c1)])
      by (eapply rw_cells_transport; [exact CV1 | exact MU2 | exact WM2 | cbn; lia]).
    assert (CF2 : rw_cells asegs m2 (spz - 72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact CF1 | exact MU2 | exact WM2 | cbn; lia]).
    assert (SV2 : SHAD m2 v (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV1 | exact MU2 | exact WM2 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      assert (sh v + 3 <= 0x10007fff8000) by (unfold sh, ASHADOW_BASE; unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA; Z.div_mod_to_equations; lia).
      lia. }
    assert (S02 : stack0 m2 lo shi).
    { eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 |].
      apply Forall_cons; [right; cbn; exact SPA|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (ST2f : stk asegs m2 lo spz).
    { apply (stk_merge asegs m2 lo (spz - 80) spz); [exact ST2 | | lia].
      eapply stk_transport_disjoint; [exact (proj2 (stk_split asegs M1 lo (spz - 80) spz ST1 ltac:(lia))) | exact MU2 | exact WM2 |].
      cbn. lia. }
    apply evt_done. exists w0, w1, w2, d0, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m2.
    split; [reflexivity|].
    split; [exact (munch_app _ _ _ _ _ MU1 MU2)|].
    split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|].
    split; [exact MI2|]. split; [exact ST2f|]. split; [exact CV2|]. split; [exact CF2|].
    split; [exact SV2|]. split; [exact S02|]. split; [exact SH2 | exact AC2].
  Qed.
End VMv1.

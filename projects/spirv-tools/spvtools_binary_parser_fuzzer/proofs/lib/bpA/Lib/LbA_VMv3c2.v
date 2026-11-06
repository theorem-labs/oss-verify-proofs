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

Definition VM1_JOIN_c2 : Z := 0xf49d4.
Definition VM1_M2_RET_c2 : Z := 0xf4a58.
Definition VM1_RET_c2 : Z := 0xf4a84.

Lemma rw_cells_of_CB_c2 : forall m A cs bs,
  rw_cells asegs m A [CB (cells_size cs) bs] -> cells_wf cs -> cells_bytes cs = bs -> rw_cells asegs m A cs.
Proof.
  intros m A cs bs [[_ HB] HW] WF EB. split; [split; [exact WF|]|].
  - cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. rewrite EB. exact HB.
  - cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW. exact HW.
Qed.

Section VMv3.
  Context {HCEIL : HeapCeil}.
  Hypothesis HMS : asan_memset_stmt.

  Lemma vm_v0_c2 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s8 s9 s10 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (spz v w lo : Z) (junk : list byte),
    rw_cells asegs m v [CB 24 junk] -> SHAD m v (repeat (b8 0) 3) -> shvis m v (v + 24) -> aapp v 24 -> v mod 8 = 0 -> v + 24 <= lo ->
    stk asegs m lo spz -> aceil <= lo -> lo <= spz - AVMOVE_STACK -> 2 ^ 45 <= spz <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR (Z_to_bv 64 VM1_JOIN_c2) (Z_to_bv 64 (spz - 80)) gp tp t0' t1' t2' (Z_to_bv 64 v) (Z_to_bv 64 w)
                      a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (v + 16)) (Z_to_bv 64 (v + 8)) (Z_to_bv 64 0x7fff8000)
                      (shw v) (shw (v + 16)) (shw (v + 8)) s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 VM1_JOIN_c2) fc None m' (seg_rom asegs)
        /\ munch [(v, v + 24); (spz - 80 - 4096, spz - 80)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo spz /\ ACONST m' /\ rw_cells asegs m' v [C8 (wz 0); C8 (wz 0); C8 (wz 0)])
      (MS (mkR (Z_to_bv 64 AVMOVE_DEL_RA_2) (Z_to_bv 64 (spz - 80)) gp tp x5 x6 x7 (Z_to_bv 64 v) (Z_to_bv 64 w)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v + 16)) (Z_to_bv 64 (v + 8)) (Z_to_bv 64 0x7fff8000)
               (shw v) (shw (v + 16)) (shw (v + 8)) s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 AVMOVE_DEL_RA_2) fc None m (seg_rom asegs)).
  Proof.
    intros until junk. intros CV SV HV VA V8 VLO ST CE LO SPR MI AC.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    unfold AVMOVE_STACK, AFREE_STACK in LO.
    pose proof (aapp_bounds v 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5). unfold AIMG_TOP in VB1.
    lazymatch goal with |- evt _ _ (MS ?T _ _ _ _ _ _) => remember T as R eqn:HR0 end.
    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 spz]).
    assert (HR : regs_ok E (srs sr_id [(8%bv, EVar 32); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-80)))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity. rewrite w_addm by lia. reflexivity. }
    assert (HK : know_ok asegs E m []) by constructor.
    xrun_at (PropExec.mkFP F fc) asegs R AVMOVE_DEL_RA_2 m (seg_rom asegs) HR HK 20%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rewrite w_addm in L2 by lia.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L8, L10, L11, L12.
    clear HRe HR' Hlf Hms HF1 L1 L2 L8 L10 L11 L12.
    eapply evt_cut.
    { eapply HMS with (c := 0) (junk := junk) (lo := lo); rewrite ?u64_of_Z by lia.
      - reflexivity.
      - lia.
      - exact CV.
      - eapply (addressable_accessible m v 24 v 24); [split; [lia | exact SV] | lia | lia | unfold AAPP_HI; lia].
      - exact HV.
      - exact (proj1 (stk_split asegs m lo (spz - 80) spz ST ltac:(lia))).
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact MI.
      - exact AC.
      - lia.
      - eapply aapp_in_app_mem; [exact VA | lia | lia].
      - eapply (aconst_ok_app v 24); [exact VA | cbn; lia | cbn; lia].
      - left; lia. }
    intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & EQ & MU & WM & MI' & ST' & CZ & AC').
    subst ms2. rewrite !u64_of_Z in MU by lia. rewrite !u64_of_Z in ST' by lia. rewrite !u64_of_Z in CZ by lia.
    unfold AINTRIN_STACK in MU. replace (spz + -80) with (spz - 80) in MU, ST' by lia.
    rewrite (ret_pc_even 1001940 ltac:(lia) eq_refl).
    apply evt_done.
    exists t0', t1', t2', (Z_to_bv 64 v), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|].
    split; [exact WM|]. split; [exact MI'|].
    split.
    { apply (stk_merge asegs m' lo (spz - 80) spz); [exact ST' | | lia].
      eapply stk_transport_disjoint; [exact (proj2 (stk_split asegs m lo (spz - 80) spz ST ltac:(lia))) | exact MU | exact WM |].
      cbn. lia. }
    split; [exact AC'|].
    eapply rw_cells_of_CB_c2; [exact CZ | cbn; tauto | reflexivity].
  Qed.
#[local] Definition HTbAVMv3c2_0 : list (reg * expr) := [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-80))); (8%bv, EVar 32); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 16)); (19%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
  Lemma vm_copy_c2 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31 : word)
      (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (spz v w b2 e2 c2 lo : Z),
    rw_cells asegs m v [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> SHAD m v (repeat (b8 0) 3) -> aapp v 24 -> v mod 8 = 0 -> v + 24 <= lo ->
    rw_cells asegs m w [C8 (wz b2); C8 (wz e2); C8 (wz c2)] -> SHAD m w (repeat (b8 0) 3) -> shvis m w (w + 24) -> w mod 8 = 0 ->
    in_app_mem w (w + 24) -> aconst_ok (w, w + 24) -> (w + 24 <= lo \/ spz <= w) -> (v + 24 <= w \/ w + 24 <= v) ->
    0x6e6000 <= w -> w + 24 <= 2 ^ 47 ->
    rw_cells asegs m (spz - 72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs m lo spz -> aceil <= lo -> lo <= spz - AVMOVE_STACK -> 2 ^ 45 <= spz <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR ra (Z_to_bv 64 spz) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(v, v + 24); (w, w + 24); (spz - 80 - 4096, spz - 80)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo spz /\ ACONST m'
        /\ rw_cells asegs m' v [C8 (wz b2); C8 (wz e2); C8 (wz c2)] /\ rw_cells asegs m' w [C8 (wz 0); C8 (wz 0); C8 (wz 0)])
      (MS (mkR x1 (Z_to_bv 64 (spz - 80)) gp tp x5 x6 x7 (Z_to_bv 64 v) (Z_to_bv 64 w) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (v + 16)) (Z_to_bv 64 (v + 8)) (Z_to_bv 64 0x7fff8000) (shw v) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 VM1_JOIN_c2) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros CV SV VA V8 VLO CW SW HVW W8 WAM WCO WAP VWD WB1 WB2 CF ST CE LO SPR MI AC.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    unfold AVMOVE_STACK, AFREE_STACK in LO.
    pose proof (aapp_bounds v 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5). unfold AIMG_TOP in VB1.

    lazymatch goal with |- evt _ _ (MS ?T _ _ _ _ _ _) => remember T as R eqn:HR0 end.
    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 spz; Z_to_bv 64 w; Z_to_bv 64 b2; Z_to_bv 64 e2; Z_to_bv 64 c2]).
    assert (HR : regs_ok E (srs sr_id HTbAVMv3c2_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity;
        unfold shw; rewrite ?w_addm, ?w_add by lia; reflexivity. }
    assert (GZV : gz m v 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
    assert (GZW : gz m w 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SW | cbn; lia]).
    assert (HK : know_ok asegs E m
       (kn_fix 20 [AASAN_MEMSET] (SCR [] [] []) VM1_JOIN_c2
          (srs sr_id HTbAVMv3c2_0)
       [ KWord (SA (EVar 34) 0) 8 (EVar 35); KWord (SA (EVar 34) 8) 8 (EVar 36); KWord (SA (EVar 34) 16) 8 (EVar 37);
         KWr (SA (EVar 32) 0) (ELit 24);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47); KRange (EVar 34) 0x6e6000 (2 ^ 47);
         KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 34) 0) (ELit 24) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CW 0%nat (C8 (wz b2)). }
      apply Forall_cons. { kword_cell CW 8%nat (C8 (wz e2)). }
      apply Forall_cons. { kword_cell CW 16%nat (C8 (wz c2)). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact (proj2 CV) | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia|].
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R VM1_JOIN_c2 m (seg_rom asegs) HR HK 200%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E VA SPR LO CE ACF1 ACF2 WB1 WB2 VLO.
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
    rreg HR' 12%bv L12. rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21.
    rewrite w_addm in L2 by lia. rewrite w_add in L18, L19 by lia.
    replace (spz + -80) with (spz - 80) in L2 by lia.
    assert (WV1 : forall a, v <= a -> a + 8 <= v + 24 -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (proj2 CV) as W. destruct W as (W1 & W2 & W). cbn [cells_size csize Z.of_nat] in W.
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (v + (a - v + i)) by lia. apply W. cbn. lia. }
    assert (MU1 : munch [(v, v + 24)] m M1).
    { subst M1. clear - Hlf VLO SPR LO CE ACF1 ACF2 VB1 VB2 VB3. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (CV1 : rw_cells asegs M1 v [C8 (wz b2); C8 (wz e2); C8 (wz c2)]).
    { subst M1. clear - Hlf WV1 VLO SPR LO CE ACF1 ACF2 VB1 VB2 VB3 VWD WB1 WB2.
      apply rw_cells_cons8_c; [lgcell Hlf (WV1 v ltac:(lia) ltac:(lia)) 2%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WV1 (v + 8) ltac:(lia) ltac:(lia)) 1%nat|].
      lgcell Hlf (WV1 (v + 8 + 8) ltac:(lia) ltac:(lia)) 0%nat. }
    assert (CW1 : rw_cells asegs M1 w [C8 (wz b2); C8 (wz e2); C8 (wz c2)])
      by (eapply rw_cells_transport; [exact CW | exact MU1 | exact WM1 | cbn; lia]).
    assert (SW1 : SHAD M1 w (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SW | exact MU1 | exact WM1 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      unfold sh, ASHADOW_BASE. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA. Z.div_mod_to_equations. lia. }
    assert (HVW1 : shvis M1 w (w + 24)).
    { eapply shvis_transport; [exact HVW | exact MU1 | exact WM1 |]. cbn.
      pose proof (hull_lo_le w ltac:(lia)) as (H1 & H2 & H3). pose proof (hull_hi_ge (w + 24) ltac:(lia)) as (G1 & G2 & G3).
      assert (LE : hull_hi (w + 24) <= 2 ^ 47 + 64) by lia.
      unfold sh, ASHADOW_BASE. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA. Z.div_mod_to_equations. lia. }
    assert (AC1 : ACONST M1).
    { eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |].
      apply Forall_cons; [eapply (aconst_ok_app v 24); [exact VA | cbn; lia | cbn; lia] | apply Forall_nil]. }
    assert (CF1 : rw_cells asegs M1 (spz - 72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact CF | exact MU1 | exact WM1 | cbn; lia]).

    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L8, L9, L10, L11, L12, L18, L19, L20, L21.
    clear HRe HR' Hlf Hms HF1 L1 L2 L8 L9 L10 L11 L12 L18 L19 L20 L21.
    eapply evt_cut.
    { eapply HMS with (c := 0) (junk := cells_bytes [C8 (wz b2); C8 (wz e2); C8 (wz c2)]) (lo := lo); rewrite ?u64_of_Z by lia.
      - reflexivity.
      - lia.
      - exact (rw_cells_to_CB _ _ _ CW1).
      - eapply (addressable_accessible M1 w 24 w 24); [split; [lia | exact SW1] | lia | lia | unfold AAPP_HI; lia].
      - exact HVW1.
      - exact (proj1 (stk_split asegs M1 lo (spz - 80) spz ST1 ltac:(lia))).
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact MI1.
      - exact AC1.
      - lia.
      - exact WAM.
      - exact WCO.
      - destruct WAP; [left | right]; lia. }
    intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & EQ & MU2 & WM2 & MI2 & ST2 & CZ & AC2).
    subst ms2. rewrite !u64_of_Z in MU2 by lia. rewrite !u64_of_Z in ST2 by lia. rewrite !u64_of_Z in CZ by lia.
    unfold AINTRIN_STACK in MU2.
    rewrite (ret_pc_even 1002072 ltac:(lia) eq_refl).
    assert (CF2 : rw_cells asegs m2 (spz - 72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact CF1 | exact MU2 | exact WM2 | cbn; destruct WAP; lia]).
    assert (CV2 : rw_cells asegs m2 v [C8 (wz b2); C8 (wz e2); C8 (wz c2)])
      by (eapply rw_cells_transport; [exact CV1 | exact MU2 | exact WM2 | cbn; lia]).
    assert (ST2f : stk asegs m2 lo spz).
    { apply (stk_merge asegs m2 lo (spz - 80) spz); [replace (spz + -80) with (spz - 80) in ST2 by lia; exact ST2 | | lia].
      eapply stk_transport_disjoint; [exact (proj2 (stk_split asegs M1 lo (spz - 80) spz ST1 ltac:(lia))) | exact MU2 | exact WM2 |].
      cbn. destruct WAP; lia. }

    lazymatch goal with |- evt _ _ (MS ?T _ _ _ _ _ _) => remember T as R2 eqn:HR2 end.
    pose (E2 := Eseed R2 [Z_to_bv 64 v; Z_to_bv 64 spz; s7; s6; s5; s4; s3; s2; s1; s0; ra]).
    assert (HR2s : regs_ok E2 (srs sr_id [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-80))); (8%bv, EVar 32)]) R2).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R2; evs; try reflexivity. rewrite w_addm by lia.
      replace (spz + -80) with (spz - 80) by lia. reflexivity. }
    assert (HK2 : know_ok asegs E2 m2
       [ KWord (SA (EVar 33) (-72)) 8 (EVar 34); KWord (SA (EVar 33) (-64)) 8 (EVar 35); KWord (SA (EVar 33) (-56)) 8 (EVar 36);
         KWord (SA (EVar 33) (-48)) 8 (EVar 37); KWord (SA (EVar 33) (-40)) 8 (EVar 38); KWord (SA (EVar 33) (-32)) 8 (EVar 39);
         KWord (SA (EVar 33) (-24)) 8 (EVar 40); KWord (SA (EVar 33) (-16)) 8 (EVar 41); KWord (SA (EVar 33) (-8)) 8 (EVar 42);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { kword_cell CF2 0%nat (C8 s7). }
      apply Forall_cons. { kword_cell CF2 8%nat (C8 s6). }
      apply Forall_cons. { kword_cell CF2 16%nat (C8 s5). }
      apply Forall_cons. { kword_cell CF2 24%nat (C8 s4). }
      apply Forall_cons. { kword_cell CF2 32%nat (C8 s3). }
      apply Forall_cons. { kword_cell CF2 40%nat (C8 s2). }
      apply Forall_cons. { kword_cell CF2 48%nat (C8 s1). }
      apply Forall_cons. { kword_cell CF2 56%nat (C8 s0). }
      apply Forall_cons. { kword_cell CF2 64%nat (C8 ra). }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R2 VM1_M2_RET_c2 m2 (seg_rom asegs) HR2s HK2 40%nat [VM1_RET_c2] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK2.
    assert (HF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF2) as HF2'. cbn [ms_regs] in HF2'.
    readback HR' HF2' HR2 HRe2.
    rreg HR' 1%bv K1. rreg HR' 2%bv K2. rreg HR' 8%bv K8. rreg HR' 9%bv K9. rreg HR' 10%bv K10. rreg HR' 18%bv K18.
    rreg HR' 19%bv K19. rreg HR' 20%bv K20. rreg HR' 21%bv K21. rreg HR' 22%bv K22. rreg HR' 23%bv K23.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe2, K1, K2, K8, K9, K10, K18, K19, K20, K21, K22, K23.
    step. apply evt_done.
    do 15 eexists. split; [reflexivity|].
    split.
    { pose proof (munch_app _ _ _ _ _ MU1 MU2) as MU. eapply munch_weaken; [| exact MU].
      intros x Hx; cbn [app outside] in Hx |- *. replace (spz + -80) with (spz - 80) in Hx by lia. lia. }
    split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|].
    split; [exact (msteps_mem_inv asegs _ _ Hms MI2)|].
    split; [exact ST2f|]. split; [exact AC2|]. split; [exact CV2|].
    eapply rw_cells_of_CB_c2; [exact CZ | cbn; tauto | reflexivity].
  Qed.

  Lemma vm_e_c2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (v w lo : Z),
    a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 w ->
    rw_cells asegs m v [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> SHAD m v (repeat (b8 0) 3) -> aapp v 24 -> v mod 8 = 0 -> v + 24 <= lo ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AVMOVE_STACK ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp x5 x6 x7 (Z_to_bv 64 v) (Z_to_bv 64 w)
                      x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v + 16)) (Z_to_bv 64 (v + 8)) (Z_to_bv 64 0x7fff8000)
                      (shw v) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 VM1_JOIN_c2) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp) /\ ACONST m'
        /\ rw_cells asegs m' v [C8 (wz 0); C8 (wz 0); C8 (wz 0)]
        /\ rw_cells asegs m' (bv_unsigned sp - 72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVMOVE_2) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros Ha0 Ha1 CV SV VA V8 VLO ST CE LO SP16 SPR MI AC.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    unfold AVMOVE_STACK, AFREE_STACK in LO.
    pose proof (aapp_bounds v 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5). unfold AIMG_TOP in VB1.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 spz; Z_to_bv 64 w]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (11%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; [exact Ha0 | exact Hsp | exact Ha1]. }
    pose proof (ACONST_shbase m AC) as [CG CS].
    assert (GZV : gz m v 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
    assert (HK : know_ok asegs E m
       (kn_fix 20 [VM1_JOIN_c2] (SCR [] [] []) AVMOVE_2 (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (11%bv, EVar 34)])
       [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
         KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
         KWord (SA (EVar 32) 0) 8 (ELit 0);
         KWr (SA (EVar 33) (-80)) (ELit 80);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47);
         KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 33) (-80)) (ELit 80) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1836e0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x18f6f8 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia|].
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R AVMOVE_2 m (seg_rom asegs) HR HK 60%nat [VM1_JOIN_c2] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E VA SPR LO CE ACF1 ACF2 VLO.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: first [ sc_shdj | sc_dj ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    rreg HR' 21%bv L21.
    rewrite w_addm in L2 by lia. rewrite w_add in L18, L19 by lia. replace (spz + -80) with (spz - 80) in L2 by lia.
    assert (WS1 : forall a, spz - 80 <= a -> a + 8 <= spz -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (wr_at_of_stk asegs m lo spz ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (MU1 : munch [(spz - 80, spz)] m M1).
    { subst M1. clear - Hlf VLO SPR LO CE ACF1 ACF2 VB1 VB2 VB3. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L2, L8, L9, L18, L19, L20, L21.
    apply evt_done.
    do 16 eexists. split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|].
    split; [exact (msteps_mem_inv asegs _ _ Hms MI)|]. split; [subst M1; apply stk_mem_denot; exact ST|].
    split; [eapply ACONST_frame; [exact AC | exact MU1 | subst M1; apply wmono_mem_denot |];
            apply Forall_cons; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity; cbn; lia | right; left; cbn; lia] | apply Forall_nil]|].
    split; [eapply rw_cells_transport; [exact CV | exact MU1 | subst M1; apply wmono_mem_denot | cbn; lia]|].
    subst M1. clear - Hlf WS1 VLO SPR LO CE ACF1 ACF2 VB1 VB2 VB3 HR0.
    apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72) ltac:(lia) ltac:(lia)) 0%nat|].
    apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8) ltac:(lia) ltac:(lia)) 1%nat|].
    apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8) ltac:(lia) ltac:(lia)) 2%nat|].
    apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 3%nat|].
    apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 4%nat|].
    apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 5%nat|].
    apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 6%nat|].
    apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 7%nat|].
    lgcell Hlf (WS1 (spz - 72 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 8%nat.
  Qed.
End VMv3.

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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX HArr.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_FKit LbA_WoR1 LbA_WoR2 LbA_WoR3 LbA_WoR4 LbA_WoR5.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_PrsStmt LbA_StateStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition WO_MS11_RA : Z := 0xea6c0.
Definition WO_MS12_RA : Z := 0xea6d0.
Definition WO_MS13_RA : Z := 0xea6e8.
Definition WO_MS14_RA : Z := 0xea6fc.
Definition WO_MS15_RA : Z := 0xea710.
Definition WO_ON7_RA : Z := 0xea718.
Definition WO_AN7_RA : Z := 0xea734.
Definition WO_ON8_RA : Z := 0xea758.
Definition WO_MC8_RA : Z := 0xea7a0.
Definition WO_AN8_RA : Z := 0xea7c4.
Definition WO_ON9_RA : Z := 0xea7f4.
Definition WO_MC9_RA : Z := 0xea83c.
Definition WO_AN9_RA : Z := 0xea860.
Definition WO_MVA2_RA : Z := 0xea880.
Definition WO_DT2_RA : Z := 0xea888.
Definition WO_DT3_RA : Z := 0xea890.
Definition WO_SF5_RA : Z := 0xea9c4.

Section WoR6.
  Context {HCEIL : HeapCeil}.

  Definition wu1_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MS11_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 120)) (Z_to_bv 64 (0)) (Z_to_bv 64 (32)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
#[local] Definition HTLbAWoR6_0 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (10%bv, EVar 35); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32))].
  Lemma wu1 : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k r : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wu1_post gp tp F fc SP S1 ff lo k r m)
      (MS (mkR (Z_to_bv 64 (AWO_PM_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (r)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 AWO_PM_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k r. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (AWO_PM_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (r)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (r)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R AWO_PM_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MS11_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (S1 + 120)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (0)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (32)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (k)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (k + 100)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (0)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wu2_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MS12_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 72)) (Z_to_bv 64 (0)) (Z_to_bv 64 (46)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
#[local] Definition HTLbAWoR6_1 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32))].
  Lemma wu2 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k r : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wu2_post gp tp F fc SP S1 ff lo k r m)
      (MS (mkR (Z_to_bv 64 (WO_MS11_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS11_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k r. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MS11_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_1) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS11_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MS12_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (S1 + 72)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (0)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (46)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (k)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (k + 100)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (0)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wu3_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MS13_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 160)) (Z_to_bv 64 (0)) (Z_to_bv 64 (32)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 152, S1 + 156)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 152) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wu3 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k r : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wu3_post gp tp F fc SP S1 ff lo k r m)
      (MS (mkR (Z_to_bv 64 (WO_MS12_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS12_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k r. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MS12_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_1) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EVar 34) 152) (ELit 4);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS12_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MS13_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (S1 + 160)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (0)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (32)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (k)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (k + 100)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (0)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [(S1 + 152, S1 + 156)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WT152 : forall a n, S1 + 152 <= a -> a + n <= S1 + 156 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (CC0 : rw_cells asegs M1 (S1 + 152) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS  WT152.
      lgc Hlf 0%nat ltac:(djd EF' ES'); first [apply WT152; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].  exact CC0.
  Qed.

  Definition wu4_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MS14_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 200)) (Z_to_bv 64 (0)) (Z_to_bv 64 (32)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 192, S1 + 196)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 192) [C4 (Z_to_bv 64 0x3f800000)].
#[local] Definition HTLbAWoR6_2 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (20%bv, ELit 1065353216)].
  Lemma wu4 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k r : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wu4_post gp tp F fc SP S1 ff lo k r m)
      (MS (mkR (Z_to_bv 64 (WO_MS13_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS13_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k r. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MS13_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_2) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EVar 34) 192) (ELit 4);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS13_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MS14_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (S1 + 200)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (0)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (32)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (k)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (k + 100)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (0)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [(S1 + 192, S1 + 196)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WT192 : forall a n, S1 + 192 <= a -> a + n <= S1 + 196 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (CC0 : rw_cells asegs M1 (S1 + 192) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS  WT192.
      lgc Hlf 0%nat ltac:(djd EF' ES'); first [apply WT192; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].  exact CC0.
  Qed.

  Definition wu5_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MS15_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 240)) (Z_to_bv 64 (0)) (Z_to_bv 64 (72)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 232, S1 + 236)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 232) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wu5 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k r : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wu5_post gp tp F fc SP S1 ff lo k r m)
      (MS (mkR (Z_to_bv 64 (WO_MS14_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS14_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k r. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MS14_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_2) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EVar 34) 232) (ELit 4);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS14_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MS15_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (S1 + 240)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (0)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (72)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (k)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (k + 100)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (0)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [(S1 + 232, S1 + 236)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WT232 : forall a n, S1 + 232 <= a -> a + n <= S1 + 236 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (CC0 : rw_cells asegs M1 (S1 + 232) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS  WT232.
      lgc Hlf 0%nat ltac:(djd EF' ES'); first [apply WT232; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].  exact CC0.
  Qed.

  Definition wu6_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_ON7_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (500)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wu6 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k r : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wu6_post gp tp F fc SP S1 ff lo k r m)
      (MS (mkR (Z_to_bv 64 (WO_MS15_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS15_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k r. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MS15_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_1) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS15_RA m (seg_rom asegs) HR HK 60%nat [AOPNEW] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_ON7_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (500)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (k)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (k + 100)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (0)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 14 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wg1a_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k r u : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_AN7_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (u)) (Z_to_bv 64 (u + 500)) (Z_to_bv 64 (u + 500)) (Z_to_bv 64 (u)) x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AANNOTATE_CC) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 240, S1 + 264)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 240) [C8 (Z_to_bv 64 u); C8 (Z_to_bv 64 u); C8 (Z_to_bv 64 (u + 500))].
  Lemma wg1a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k r u : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    0 < u /\ u + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wg1a_post gp tp F fc SP S1 ff lo k r u m)
      (MS (mkR (Z_to_bv 64 (WO_ON7_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (u)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_ON7_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k r u. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Bu ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_ON7_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (u)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (u)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EVar 34) 240) (ELit 24);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON7_RA m (seg_rom asegs) HR HK 60%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_AN7_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (u)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (u + 500)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (u + 500)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 13%bv L13.
    assert (L13' : getr R' 13 = Z_to_bv 64 (u)) by (rewrite L13; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (k)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (k + 100)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (0)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [(S1 + 240, S1 + 264)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WT240 : forall a n, S1 + 240 <= a -> a + n <= S1 + 264 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (CC0 : rw_cells asegs M1 (S1 + 240) [C8 (Z_to_bv 64 u); C8 (Z_to_bv 64 u); C8 (Z_to_bv 64 (u + 500))]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS Bu WT240.
      apply rw_cells_cons8_c; [lgc Hlf 2%nat ltac:(djd EF' ES'); first [apply WT240; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      apply rw_cells_cons8_c; [lgc Hlf 1%nat ltac:(djd EF' ES'); first [apply WT240; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      lgc Hlf 0%nat ltac:(djd EF' ES'); first [apply WT240; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L13', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 11 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].  exact CC0.
  Qed.

  Definition wg1b_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_ON8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (100)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wg1b : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k r : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 264) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 280) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 272) [CB 8 (poison_bytes 8 0)] ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wg1b_post gp tp F fc SP S1 ff lo k r m)
      (MS (mkR (Z_to_bv 64 (WO_AN7_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_AN7_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k r. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs264 Zs280 Zs272 ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_AN7_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_1) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EVar 34) 264) 8 (ELit 0);
        KWord (SA (EVar 34) 280) 8 (ELit 0);
        KWord (SA (EVar 34) 272) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 264) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs264 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 280) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs280 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 272) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs272 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN7_RA m (seg_rom asegs) HR HK 60%nat [AOPNEW] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_ON8_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (100)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (k)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (0)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (0)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 14 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wg2a_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k r v : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MC8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (v)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (v)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (v)) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
#[local] Definition HTLbAWoR6_3 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (10%bv, EVar 35); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (24%bv, ELit 0)].
  Lemma wg2a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k r v : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 264) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 272) [CB 8 (poison_bytes 8 0)] ->
    0 < v /\ v + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wg2a_post gp tp F fc SP S1 ff lo k r v m)
      (MS (mkR (Z_to_bv 64 (WO_ON8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (v)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_ON8_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k r v. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs264 Zs272 Bv ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_ON8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (v)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (v)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_3) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EVar 34) 264) 8 (ELit 0);
        KWord (SA (EVar 34) 272) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 264) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs264 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 272) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs272 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON8_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMCPY] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MC8_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (v)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (0)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (0)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (v)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (v)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (v + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wg2b_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo r v : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_AN8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (v)) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 (v)) x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (v)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (v)) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AANNOTATE_CC) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 264, S1 + 288)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 264) [C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 (v + 100))].
#[local] Definition HTLbAWoR6_4 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (21%bv, EVar 35); (24%bv, EVar 35); (25%bv, EAlu ALU_ADD (EVar 35) (ELit 100)); (26%bv, ELit 0)].
  Lemma wg2b : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo r v : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 280) [CB 8 (poison_bytes 8 0)] ->
    0 < v /\ v + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wg2b_post gp tp F fc SP S1 ff lo r v m)
      (MS (mkR (Z_to_bv 64 (WO_MC8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (v)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (v)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (v)) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MC8_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo r v. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs280 Bv ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MC8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (v)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (v)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (v)) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (v)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_4) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EVar 34) 264) (ELit 24);
        KWord (SA (EVar 34) 280) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 280) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs280 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MC8_RA m (seg_rom asegs) HR HK 60%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_AN8_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (v)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (v + 100)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (v + 100)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 13%bv L13.
    assert (L13' : getr R' 13 = Z_to_bv 64 (v)) by (rewrite L13; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (v)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (v)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (v + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [(S1 + 264, S1 + 288)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WT264 : forall a n, S1 + 264 <= a -> a + n <= S1 + 288 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (CC0 : rw_cells asegs M1 (S1 + 264) [C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 (v + 100))]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS Zs280 Bv WT264.
      apply rw_cells_cons8_c; [lgc Hlf 2%nat ltac:(djd EF' ES'); first [apply WT264; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      apply rw_cells_cons8_c; [lgc Hlf 1%nat ltac:(djd EF' ES'); first [apply WT264; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      lgc Hlf 0%nat ltac:(djd EF' ES'); first [apply WT264; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L13', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 11 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].  exact CC0.
  Qed.

  Definition wg2c_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo r v : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_ON9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (100)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (v)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (0)) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wg2c : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo r v : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 288) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 304) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 296) [CB 8 (poison_bytes 8 0)] ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wg2c_post gp tp F fc SP S1 ff lo r v m)
      (MS (mkR (Z_to_bv 64 (WO_AN8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (v)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (v)) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_AN8_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo r v. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs288 Zs304 Zs296 ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_AN8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (v)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (v)) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (22%bv, ELit 99); (26%bv, ELit 0)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EVar 34) 288) 8 (ELit 0);
        KWord (SA (EVar 34) 304) 8 (ELit 0);
        KWord (SA (EVar 34) 296) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 288) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs288 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 304) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs304 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 296) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs296 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN8_RA m (seg_rom asegs) HR HK 60%nat [AOPNEW] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_ON9_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (100)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (v)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (0)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (v + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 14 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wg3a_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo r v w : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MC9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (w)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wg3a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo r v w : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 288) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 296) [CB 8 (poison_bytes 8 0)] ->
    0 < w /\ w + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wg3a_post gp tp F fc SP S1 ff lo r v w m)
      (MS (mkR (Z_to_bv 64 (WO_ON9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (w)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (v)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (0)) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_ON9_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo r v w. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs288 Zs296 Bw ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_ON9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (w)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (v)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (0)) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (w)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_3) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EVar 34) 288) 8 (ELit 0);
        KWord (SA (EVar 34) 296) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 288) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs288 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 296) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs296 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON9_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMCPY] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MC9_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (w)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (0)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (0)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (w)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (w)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (w + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wg3b_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo r w : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_AN9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (w)) x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AANNOTATE_CC) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 288, S1 + 312)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 288) [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 (w + 100))].
  Lemma wg3b : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo r w : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 304) [CB 8 (poison_bytes 8 0)] ->
    0 < w /\ w + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wg3b_post gp tp F fc SP S1 ff lo r w m)
      (MS (mkR (Z_to_bv 64 (WO_MC9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (w)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MC9_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo r w. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs304 Bw ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MC9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (w)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (w)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_4) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EVar 34) 288) (ELit 24);
        KWord (SA (EVar 34) 304) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 304) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zs304 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MC9_RA m (seg_rom asegs) HR HK 60%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_AN9_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (w)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (w + 100)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (w + 100)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 13%bv L13.
    assert (L13' : getr R' 13 = Z_to_bv 64 (w)) by (rewrite L13; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (w)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (w)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (w + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [(S1 + 288, S1 + 312)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WT288 : forall a n, S1 + 288 <= a -> a + n <= S1 + 312 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (CC0 : rw_cells asegs M1 (S1 + 288) [C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 (w + 100))]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS Zs304 Bw WT288.
      apply rw_cells_cons8_c; [lgc Hlf 2%nat ltac:(djd EF' ES'); first [apply WT288; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      apply rw_cells_cons8_c; [lgc Hlf 1%nat ltac:(djd EF' ES'); first [apply WT288; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      lgc Hlf 0%nat ltac:(djd EF' ES'); first [apply WT288; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L13', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 11 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].  exact CC0.
  Qed.

  Definition wg3c_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo r w : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MVA2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (S1 + 72)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_MVA) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wg3c : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo r w : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 48) [C8 (Z_to_bv 64 (ff + 176))] ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wg3c_post gp tp F fc SP S1 ff lo r w m)
      (MS (mkR (Z_to_bv 64 (WO_AN9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_AN9_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo r w. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP S48 ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_AN9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (26%bv, ELit 0)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EVar 34) 48) 8 (EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 176));
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 48) _ 0%nat (C8 (Z_to_bv 64 (ff + 176)))); [exact S48 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN9_RA m (seg_rom asegs) HR HK 60%nat [AST_MVA] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MVA2_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 176)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (S1 + 72)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (ff + 176)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (w)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (w)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (w + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wd3_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo r w : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_DT2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 72)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_DTOR) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wd3 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo r w : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wd3_post gp tp F fc SP S1 ff lo r w m)
      (MS (mkR (Z_to_bv 64 (WO_MVA2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MVA2_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo r w. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MVA2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_1) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MVA2_RA m (seg_rom asegs) HR HK 60%nat [AST_DTOR] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_DT2_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (S1 + 72)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (ff + 176)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (w)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (w)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (w + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 14 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wd4_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo r w : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_DT3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (ff + 176)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_DTOR) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wd4 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo r w : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wd4_post gp tp F fc SP S1 ff lo r w m)
      (MS (mkR (Z_to_bv 64 (WO_DT2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_DT2_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo r w. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_DT2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (20%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 176))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_DT2_RA m (seg_rom asegs) HR HK 60%nat [AST_DTOR] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_DT3_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 176)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (ff + 176)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (w)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (w)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (w + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 14 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition we1_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo r w : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_SF5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (64)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 ASET_SHADOW_F5) fc None m1 (seg_rom asegs)
      /\ munch [(sh ff + 4, sh ff + 52); (ff, ff + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma we1 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo r w : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    wr_at asegs m (ff + 0) 8 ->
    rw_cells asegs m (S1 + 24) [C8 (Z_to_bv 64 (ff + 32))] ->
    rw_cells asegs m (ff + 80) [C8 (Z_to_bv 64 (0))] ->
    rw_cells asegs m (S1 + 56) [C8 (Z_to_bv 64 (ff + 48))] ->
    rw_cells asegs m (S1 + 40) [C8 (Z_to_bv 64 (ff))] ->
    rw_cells asegs m (S1 + 32) [C8 (Z_to_bv 64 (0x7fff8000))] ->
    wr_at asegs m (sh ff + 4) 48 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we1_post gp tp F fc SP S1 ff lo r w m)
      (MS (mkR (Z_to_bv 64 (WO_DT3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_DT3_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo r w. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP WF0 S24 F80 S56 S40 S32 WH4 ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_DT3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (w)) (Z_to_bv 64 (99)) (Z_to_bv 64 (r)) (Z_to_bv 64 (w)) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR6_1) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 8);
        KWord (SA (EVar 34) 24) 8 (EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 32));
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 80) 8 (ELit 0);
        KWord (SA (EVar 34) 56) 8 (EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 48));
        KWord (SA (EVar 34) 40) 8 (EMd M_MUL (ELit 64) (EVar 32));
        KWord (SA (EVar 34) 32) 8 (ELit 2147450880);
        KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) (SHBASE + 4)) (ELit 48);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF0 | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 24) _ 0%nat (C8 (Z_to_bv 64 (ff + 32)))); [exact S24 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 80) _ 0%nat (C8 (Z_to_bv 64 (0)))); [exact F80 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 56) _ 0%nat (C8 (Z_to_bv 64 (ff + 48)))); [exact S56 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 40) _ 0%nat (C8 (Z_to_bv 64 (ff)))); [exact S40 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; rewrite ?Q; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 32) _ 0%nat (C8 (Z_to_bv 64 (0x7fff8000)))); [exact S32 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WH4 | unfold estart; cbn [a_base a_off]; evs; rewrite ES'; unfold SHBASE; lia | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite ES', u64_of_Z by lia; unfold SHBASE; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_DT3_RA m (seg_rom asegs) HR HK 120%nat [ASET_SHADOW_F5] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_SF5_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (sh ff)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (64)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (ff)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (w)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (r)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (w)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (w + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [(sh ff + 4, sh ff + 52); (ff, ff + 8)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WS0 : forall a n, ff + 0 <= a -> a + n <= ff + 8 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WF0 as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 0 + (a - (ff + 0) + i)) by lia. apply W. lia. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

End WoR6.

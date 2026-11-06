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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_FKit LbA_WoR1 LbA_WoR2 LbA_WoR3 LbA_WoR4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_PrsStmt LbA_StateStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition WO_MS7_RA : Z := 0xea4f0.
Definition WO_MS8_RA : Z := 0xea508.
Definition WO_MS9_RA : Z := 0xea51c.
Definition WO_MS10_RA : Z := 0xea530.
Definition WO_ON4_RA : Z := 0xea538.
Definition WO_AN4_RA : Z := 0xea554.
Definition WO_ON5_RA : Z := 0xea578.
Definition WO_MC5_RA : Z := 0xea5c0.
Definition WO_AN5_RA : Z := 0xea5e4.
Definition WO_ON6_RA : Z := 0xea614.
Definition WO_MC6_RA : Z := 0xea65c.
Definition WO_AN6_RA : Z := 0xea680.
Definition WO_MVA1_RA : Z := 0xea69c.
Definition WO_DT1_RA : Z := 0xea6a4.

Section WoR5.
  Context {HCEIL : HeapCeil}.

  Definition wt1_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo d : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MS7_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (0)) (Z_to_bv 64 (22)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wt1 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo d : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wt1_post gp tp F fc SP S1 ff lo d m)
      (MS (mkR (Z_to_bv 64 (WO_MS6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS6_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo d. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MS6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (21%bv, EAlu ALU_ADD (EVar 34) (ELit 96))]) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS6_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MS7_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (S1 + 96)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (0)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (22)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (S1 + 96)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (d)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (d + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition wt2_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo d : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MS8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 160)) (Z_to_bv 64 (0)) (Z_to_bv 64 (32)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 152, S1 + 156)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 152) [C4 (Z_to_bv 64 0x3f800000)].
#[local] Definition HTLbAWoR5_0 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32))].
  Lemma wt2 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo d : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wt2_post gp tp F fc SP S1 ff lo d m)
      (MS (mkR (Z_to_bv 64 (WO_MS7_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS7_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo d. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MS7_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR5_0) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS7_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MS8_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (S1 + 96)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (d)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (d + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition wt3_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo d : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MS9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 200)) (Z_to_bv 64 (0)) (Z_to_bv 64 (32)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 192, S1 + 196)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 192) [C4 (Z_to_bv 64 0x3f800000)].
#[local] Definition HTLbAWoR5_1 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (20%bv, ELit 1065353216)].
  Lemma wt3 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo d : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wt3_post gp tp F fc SP S1 ff lo d m)
      (MS (mkR (Z_to_bv 64 (WO_MS8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS8_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo d. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MS8_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR5_1) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS8_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MS9_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (S1 + 96)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (d)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (d + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition wt4_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo d : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MS10_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 240)) (Z_to_bv 64 (0)) (Z_to_bv 64 (72)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 232, S1 + 236)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 232) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wt4 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo d : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wt4_post gp tp F fc SP S1 ff lo d m)
      (MS (mkR (Z_to_bv 64 (WO_MS9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS9_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo d. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MS9_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR5_1) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS9_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MS10_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (S1 + 96)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (d)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (d + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition wt5_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo d : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_ON4_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (500)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wt5 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo d : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wt5_post gp tp F fc SP S1 ff lo d m)
      (MS (mkR (Z_to_bv 64 (WO_MS10_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS10_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo d. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MS10_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR5_0) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS10_RA m (seg_rom asegs) HR HK 60%nat [AOPNEW] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_ON4_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (S1 + 96)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (d)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (d + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition wf1a_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo d g : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_AN4_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (g)) (Z_to_bv 64 (g + 500)) (Z_to_bv 64 (g + 500)) (Z_to_bv 64 (g)) x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AANNOTATE_CC) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 240, S1 + 264)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 240) [C8 (Z_to_bv 64 g); C8 (Z_to_bv 64 g); C8 (Z_to_bv 64 (g + 500))].
  Lemma wf1a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo d g : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    0 < g /\ g + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wf1a_post gp tp F fc SP S1 ff lo d g m)
      (MS (mkR (Z_to_bv 64 (WO_ON4_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (g)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_ON4_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo d g. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Bg ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_ON4_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (g)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (g)]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (10%bv, EVar 35); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32))]) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON4_RA m (seg_rom asegs) HR HK 60%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_AN4_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (g)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (g + 500)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (g + 500)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 13%bv L13.
    assert (L13' : getr R' 13 = Z_to_bv 64 (g)) by (rewrite L13; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (S1 + 96)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (d)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (d + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (CC0 : rw_cells asegs M1 (S1 + 240) [C8 (Z_to_bv 64 g); C8 (Z_to_bv 64 g); C8 (Z_to_bv 64 (g + 500))]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS Bg WT240.
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

  Definition wf1b_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo d : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_ON5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (100)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wf1b : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo d : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 264) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 280) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 272) [CB 8 (poison_bytes 8 0)] ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wf1b_post gp tp F fc SP S1 ff lo d m)
      (MS (mkR (Z_to_bv 64 (WO_AN4_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_AN4_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo d. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs264 Zs280 Zs272 ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_AN4_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR5_0) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN4_RA m (seg_rom asegs) HR HK 60%nat [AOPNEW] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_ON5_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (S1 + 96)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (d)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (d + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition wf2a_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo d h : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MC5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (h)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (h)) (Z_to_bv 64 (99)) (Z_to_bv 64 (h)) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
#[local] Definition HTLbAWoR5_2 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (10%bv, EVar 35); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (23%bv, ELit 0)].
  Lemma wf2a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo d h : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 264) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 272) [CB 8 (poison_bytes 8 0)] ->
    0 < h /\ h + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wf2a_post gp tp F fc SP S1 ff lo d h m)
      (MS (mkR (Z_to_bv 64 (WO_ON5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (h)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_ON5_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo d h. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs264 Zs272 Bh ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_ON5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (h)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (h)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR5_2) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON5_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMCPY] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MC5_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (h)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (h)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (h)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (h + 100)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition wf2b_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo h : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_AN5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (h)) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 (h)) x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (h)) (Z_to_bv 64 (99)) (Z_to_bv 64 (h)) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AANNOTATE_CC) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 264, S1 + 288)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 264) [C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 (h + 100))].
#[local] Definition HTLbAWoR5_3 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (21%bv, EVar 35); (23%bv, EVar 35); (24%bv, EAlu ALU_ADD (EVar 35) (ELit 100)); (25%bv, ELit 0)].
  Lemma wf2b : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo h : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 280) [CB 8 (poison_bytes 8 0)] ->
    0 < h /\ h + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wf2b_post gp tp F fc SP S1 ff lo h m)
      (MS (mkR (Z_to_bv 64 (WO_MC5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (h)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (h)) (Z_to_bv 64 (99)) (Z_to_bv 64 (h)) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MC5_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo h. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs280 Bh ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MC5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (h)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (h)) (Z_to_bv 64 (99)) (Z_to_bv 64 (h)) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (h)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR5_3) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_MC5_RA m (seg_rom asegs) HR HK 60%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_AN5_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (h)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (h + 100)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (h + 100)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 13%bv L13.
    assert (L13' : getr R' 13 = Z_to_bv 64 (h)) by (rewrite L13; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (h)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (h)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (h + 100)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (0)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (CC0 : rw_cells asegs M1 (S1 + 264) [C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 (h + 100))]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS Zs280 Bh WT264.
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

  Definition wf2c_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo h : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_ON6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (100)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (h)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wf2c : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo h : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 288) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 304) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 296) [CB 8 (poison_bytes 8 0)] ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wf2c_post gp tp F fc SP S1 ff lo h m)
      (MS (mkR (Z_to_bv 64 (WO_AN5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (h)) (Z_to_bv 64 (99)) (Z_to_bv 64 (h)) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_AN5_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo h. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs288 Zs304 Zs296 ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_AN5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (h)) (Z_to_bv 64 (99)) (Z_to_bv 64 (h)) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (22%bv, ELit 99); (25%bv, ELit 0)]) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN5_RA m (seg_rom asegs) HR HK 60%nat [AOPNEW] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_ON6_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (h)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (h + 100)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition wf3a_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo h k : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MC6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (k)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wf3a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo h k : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 288) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (S1 + 296) [CB 8 (poison_bytes 8 0)] ->
    0 < k /\ k + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wf3a_post gp tp F fc SP S1 ff lo h k m)
      (MS (mkR (Z_to_bv 64 (WO_ON6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (k)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (h)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_ON6_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo h k. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs288 Zs296 Bk ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_ON6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (k)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (h)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (k)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR5_2) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON6_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMCPY] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MC6_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (k)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (k)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (k)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition wf3b_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_AN6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (k)) x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AANNOTATE_CC) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 288, S1 + 312)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 288) [C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 (k + 100))].
  Lemma wf3b : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 304) [CB 8 (poison_bytes 8 0)] ->
    0 < k /\ k + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wf3b_post gp tp F fc SP S1 ff lo k m)
      (MS (mkR (Z_to_bv 64 (WO_MC6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (k)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MC6_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zs304 Bk ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MC6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (k)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (k)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR5_3) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_MC6_RA m (seg_rom asegs) HR HK 60%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_AN6_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (k)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (k + 100)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (k + 100)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 13%bv L13.
    assert (L13' : getr R' 13 = Z_to_bv 64 (k)) by (rewrite L13; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L23' : getr R' 23 = Z_to_bv 64 (k)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (k + 100)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (0)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (CC0 : rw_cells asegs M1 (S1 + 288) [C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 (k + 100))]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS Zs304 Bk WT288.
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

  Definition wf3c_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MVA1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (S1 + 72)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_MVA) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wf3c : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 48) [C8 (Z_to_bv 64 (ff + 176))] ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wf3c_post gp tp F fc SP S1 ff lo k m)
      (MS (mkR (Z_to_bv 64 (WO_AN6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_AN6_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP S48 ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_AN6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (25%bv, ELit 0)]) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN6_RA m (seg_rom asegs) HR HK 60%nat [AST_MVA] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MVA1_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (k)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (k)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wd1_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_DT1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 72)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_DTOR) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wd1 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wd1_post gp tp F fc SP S1 ff lo k m)
      (MS (mkR (Z_to_bv 64 (WO_MVA1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MVA1_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MVA1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR5_0) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_MVA1_RA m (seg_rom asegs) HR HK 60%nat [AST_DTOR] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_DT1_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (k)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (k)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition wd2_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo k : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (AWO_PM_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (ff + 128)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 APM_ENTRY) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wd2 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo k : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wd2_post gp tp F fc SP S1 ff lo k m)
      (MS (mkR (Z_to_bv 64 (WO_DT1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_DT1_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo k. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP  ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_DT1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (k)) (Z_to_bv 64 (99)) (Z_to_bv 64 (k)) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (27%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 128))]) R).
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
    xrun_at (PropExec.mkFP F fc) asegs R WO_DT1_RA m (seg_rom asegs) HR HK 60%nat [APM_ENTRY] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (AWO_PM_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 128)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L23' : getr R' 23 = Z_to_bv 64 (k)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

End WoR5.

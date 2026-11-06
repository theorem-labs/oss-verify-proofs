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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_FKit LbA_WoR1 LbA_WoR2 LbA_WoR3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition WO_MC1_RA : Z := 0xea334.
Definition WO_AN1_RA : Z := 0xea358.
Definition WO_ON2_RA : Z := 0xea38c.
Definition WO_MC2_RA : Z := 0xea3d4.
Definition WO_AN2_RA : Z := 0xea3f8.
Definition WO_ON3_RA : Z := 0xea428.
Definition WO_MC3_RA : Z := 0xea470.
Definition WO_AN3_RA : Z := 0xea494.
Definition WO_MS6_RA : Z := 0xea4e0.

Section WoR4.
  Context {HCEIL : HeapCeil}.

  Definition we1a_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo b : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MC1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (b)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (b)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (b)) (Z_to_bv 64 (b + 500)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
#[local] Definition HTLbAWoR4_0 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (10%bv, EVar 35); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (24%bv, ELit 0); (27%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 128))].
  Lemma we1a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo b : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (ff + 344) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (ff + 352) [CB 8 (poison_bytes 8 0)] ->
    0 < b /\ b + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we1a_post gp tp F fc SP S1 ff lo b m)
      (MS (mkR (Z_to_bv 64 (WO_ON1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (b)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (0x7fff8000)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_ON1_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo b. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zf344 Zf352 Bb ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_ON1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (b)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (0x7fff8000)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (b)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR4_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 344) 8 (ELit 0);
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 352) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 344) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf344 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 352) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf352 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON1_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMCPY] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MC1_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (b)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (b)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (0)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (b)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (b + 500)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition we1b_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo b : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_AN1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (b)) (Z_to_bv 64 (b + 500)) (Z_to_bv 64 (b + 500)) (Z_to_bv 64 (b)) x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (b)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (b)) (Z_to_bv 64 (b + 500)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AANNOTATE_CC) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 344, ff + 368)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 344) [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 (b + 500))].
  Lemma we1b : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo b : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    wr_at asegs m (ff + 344) 24 ->
    rw_cells asegs m (ff + 360) [CB 8 (poison_bytes 8 0)] ->
    0 < b /\ b + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we1b_post gp tp F fc SP S1 ff lo b m)
      (MS (mkR (Z_to_bv 64 (WO_MC1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (b)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (b)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (b)) (Z_to_bv 64 (b + 500)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MC1_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo b. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP WF344 Zf360 Bb ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MC1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (b)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (b)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (b)) (Z_to_bv 64 (b + 500)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (b)]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (21%bv, EVar 35); (24%bv, EVar 35); (25%bv, EAlu ALU_ADD (EVar 35) (ELit 500)); (26%bv, ELit 0); (27%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 128))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 344) (ELit 24);
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 360) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF344 | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 360) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf360 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MC1_RA m (seg_rom asegs) HR HK 60%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_AN1_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (b)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (b + 500)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (b + 500)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 13%bv L13.
    assert (L13' : getr R' 13 = Z_to_bv 64 (b)) by (rewrite L13; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (b)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (0)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (b)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (b + 500)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [(ff + 344, ff + 368)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WS344 : forall a n, ff + 344 <= a -> a + n <= ff + 368 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WF344 as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 344 + (a - (ff + 344) + i)) by lia. apply W. lia. }
    assert (CC0 : rw_cells asegs M1 (ff + 344) [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 (b + 500))]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS Zf360 Bb WS344.
      apply rw_cells_cons8_c; [lgc Hlf 2%nat ltac:(djd EF' ES'); first [apply WS344; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      apply rw_cells_cons8_c; [lgc Hlf 1%nat ltac:(djd EF' ES'); first [apply WS344; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      lgc Hlf 0%nat ltac:(djd EF' ES'); first [apply WS344; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L13', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 11 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].  exact CC0.
  Qed.

  Definition we1c_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo b : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_ON2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (100)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (b)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (b + 500)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma we1c : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo b : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (ff + 368) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (ff + 376) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (ff + 384) [CB 8 (poison_bytes 8 0)] ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we1c_post gp tp F fc SP S1 ff lo b m)
      (MS (mkR (Z_to_bv 64 (WO_AN1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (b)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (b)) (Z_to_bv 64 (b + 500)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_AN1_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo b. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zf368 Zf376 Zf384 ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_AN1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (b)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (b)) (Z_to_bv 64 (b + 500)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (26%bv, ELit 0); (27%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 128))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 368) 8 (ELit 0);
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 376) 8 (ELit 0);
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 384) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 368) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf368 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 376) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf376 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 384) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf384 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN1_RA m (seg_rom asegs) HR HK 60%nat [AOPNEW] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_ON2_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (b)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (0)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (b + 500)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition we2a_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo b c : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MC2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (c)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (c)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma we2a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo b c : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (ff + 368) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (ff + 376) [CB 8 (poison_bytes 8 0)] ->
    0 < c /\ c + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we2a_post gp tp F fc SP S1 ff lo b c m)
      (MS (mkR (Z_to_bv 64 (WO_ON2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (c)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (b)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (b + 500)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_ON2_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo b c. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zf368 Zf376 Bc ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_ON2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (c)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (b)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (b + 500)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (c)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR4_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 368) 8 (ELit 0);
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 376) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 368) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf368 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 376) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf376 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON2_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMCPY] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MC2_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (c)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (c)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (c)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (c + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition we2b_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo c : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_AN2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (c)) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 (c)) x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AANNOTATE_CC) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 368, ff + 392)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 368) [C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 (c + 100))].
#[local] Definition HTLbAWoR4_1 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (21%bv, EVar 35); (24%bv, EVar 35); (25%bv, EAlu ALU_ADD (EVar 35) (ELit 100)); (26%bv, ELit 0); (27%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 128))].
  Lemma we2b : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo c : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    wr_at asegs m (ff + 368) 24 ->
    rw_cells asegs m (ff + 384) [CB 8 (poison_bytes 8 0)] ->
    0 < c /\ c + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we2b_post gp tp F fc SP S1 ff lo c m)
      (MS (mkR (Z_to_bv 64 (WO_MC2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (c)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (c)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MC2_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo c. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP WF368 Zf384 Bc ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MC2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (c)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (c)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (c)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR4_1) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 368) (ELit 24);
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 384) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF368 | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 384) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf384 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MC2_RA m (seg_rom asegs) HR HK 60%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_AN2_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (c)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (c + 100)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (c + 100)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 13%bv L13.
    assert (L13' : getr R' 13 = Z_to_bv 64 (c)) by (rewrite L13; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (c)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (c)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (c + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (0)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 27%bv L27.
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    assert (MU1 : munch [(ff + 368, ff + 392)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WS368 : forall a n, ff + 368 <= a -> a + n <= ff + 392 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WF368 as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 368 + (a - (ff + 368) + i)) by lia. apply W. lia. }
    assert (CC0 : rw_cells asegs M1 (ff + 368) [C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 (c + 100))]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS Zf384 Bc WS368.
      apply rw_cells_cons8_c; [lgc Hlf 2%nat ltac:(djd EF' ES'); first [apply WS368; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      apply rw_cells_cons8_c; [lgc Hlf 1%nat ltac:(djd EF' ES'); first [apply WS368; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      lgc Hlf 0%nat ltac:(djd EF' ES'); first [apply WS368; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L13', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 11 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].  exact CC0.
  Qed.

  Definition we2c_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo c : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_ON3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (100)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma we2c : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo c : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (ff + 392) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (ff + 400) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (ff + 408) [CB 8 (poison_bytes 8 0)] ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we2c_post gp tp F fc SP S1 ff lo c m)
      (MS (mkR (Z_to_bv 64 (WO_AN2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_AN2_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo c. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zf392 Zf400 Zf408 ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_AN2_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (22%bv, ELit 99); (26%bv, ELit 0); (27%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 128))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 392) 8 (ELit 0);
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 400) 8 (ELit 0);
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 408) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 392) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf392 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 400) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf400 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 408) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf408 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN2_RA m (seg_rom asegs) HR HK 60%nat [AOPNEW] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_ON3_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (c)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (99)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (0)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (c + 100)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition we3a_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo c d : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MC3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (d)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma we3a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo c d : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (ff + 392) [CB 8 (poison_bytes 8 0)] ->
    rw_cells asegs m (ff + 400) [CB 8 (poison_bytes 8 0)] ->
    0 < d /\ d + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we3a_post gp tp F fc SP S1 ff lo c d m)
      (MS (mkR (Z_to_bv 64 (WO_ON3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (d)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_ON3_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo c d. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Zf392 Zf400 Bd ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_ON3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (d)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (d)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR4_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 392) 8 (ELit 0);
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 400) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 392) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf392 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 400) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf400 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON3_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMCPY] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MC3_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (d)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (d)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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

  Definition we3b_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo d : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_AN3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (d)) x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AANNOTATE_CC) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 392, ff + 416)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 392) [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 (d + 100))].
  Lemma we3b : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo d : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    wr_at asegs m (ff + 392) 24 ->
    rw_cells asegs m (ff + 408) [CB 8 (poison_bytes 8 0)] ->
    0 < d /\ d + 512 < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we3b_post gp tp F fc SP S1 ff lo d m)
      (MS (mkR (Z_to_bv 64 (WO_MC3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (d)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MC3_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo d. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP WF392 Zf408 Bd ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MC3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (d)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (d)]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR4_1) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 392) (ELit 24);
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 408) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF392 | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 408) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Zf408 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MC3_RA m (seg_rom asegs) HR HK 60%nat [AANNOTATE_CC] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_AN3_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 2%bv L2.
    assert (L2' : getr R' 2 = Z_to_bv 64 (S1)) by (rewrite L2; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 8%bv L8.
    assert (L8' : getr R' 8 = Z_to_bv 64 (SP)) by (rewrite L8; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 9%bv L9.
    assert (L9' : getr R' 9 = Z_to_bv 64 (S1)) by (rewrite L9; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (d)) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 11%bv L11.
    assert (L11' : getr R' 11 = Z_to_bv 64 (d + 100)) by (rewrite L11; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 12%bv L12.
    assert (L12' : getr R' 12 = Z_to_bv 64 (d + 100)) by (rewrite L12; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 13%bv L13.
    assert (L13' : getr R' 13 = Z_to_bv 64 (d)) by (rewrite L13; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 18%bv L18.
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 19%bv L19.
    assert (L19' : getr R' 19 = Z_to_bv 64 (ff)) by (rewrite L19; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 20%bv L20.
    assert (L20' : getr R' 20 = Z_to_bv 64 (0)) by (rewrite L20; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 21%bv L21.
    assert (L21' : getr R' 21 = Z_to_bv 64 (d)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (MU1 : munch [(ff + 392, ff + 416)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WS392 : forall a n, ff + 392 <= a -> a + n <= ff + 416 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WF392 as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 392 + (a - (ff + 392) + i)) by lia. apply W. lia. }
    assert (CC0 : rw_cells asegs M1 (ff + 392) [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 (d + 100))]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS Zf408 Bd WS392.
      apply rw_cells_cons8_c; [lgc Hlf 2%nat ltac:(djd EF' ES'); first [apply WS392; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      apply rw_cells_cons8_c; [lgc Hlf 1%nat ltac:(djd EF' ES'); first [apply WS392; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      lgc Hlf 0%nat ltac:(djd EF' ES'); first [apply WS392; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L13', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 11 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].  exact CC0.
  Qed.

  Definition we3c_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo d words nw : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_MS6_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (S1 + 120)) (Z_to_bv 64 (0)) (Z_to_bv 64 (32)) x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (S1 + 96)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 72, S1 + 96)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 72) [C8 (Z_to_bv 64 words); C8 (Z_to_bv 64 nw); C8 (Z_to_bv 64 0)].
  Lemma we3c : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo d words nw : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (S1 + 0) [C8 (Z_to_bv 64 (0))] ->
    rw_cells asegs m (S1 + 8) [C8 (Z_to_bv 64 (words))] ->
    rw_cells asegs m (S1 + 16) [C8 (Z_to_bv 64 (nw))] ->
    0 <= words < 2 ^ 64 /\ 0 <= nw < 2 ^ 64 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we3c_post gp tp F fc SP S1 ff lo d words nw m)
      (MS (mkR (Z_to_bv 64 (WO_AN3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_AN3_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo d words nw. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Sop Swd Snn Bwn ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_AN3_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (99)) (Z_to_bv 64 (0)) (Z_to_bv 64 (d)) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 (0); Z_to_bv 64 (words); Z_to_bv 64 (nw)]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (23%bv, ELit 0); (26%bv, ELit 0)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EVar 34) 72) (ELit 24);
        KWord (SA (EVar 34) 0) 8 (ELit 0);
        KWord (SA (EVar 34) 8) 8 (EVar 36);
        KWord (SA (EVar 34) 16) 8 (EVar 37);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 0) _ 0%nat (C8 (Z_to_bv 64 (0)))); [exact Sop | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; rewrite ?Q, ?w_add, ?v_addi_Z, ?u64_of_Z by lia; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 8) _ 0%nat (C8 (Z_to_bv 64 (words)))); [exact Swd | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 16) _ 0%nat (C8 (Z_to_bv 64 (nw)))); [exact Snn | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN3_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_MS6_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (MU1 : munch [(S1 + 72, S1 + 96)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WT72 : forall a n, S1 + 72 <= a -> a + n <= S1 + 96 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (CC0 : rw_cells asegs M1 (S1 + 72) [C8 (Z_to_bv 64 words); C8 (Z_to_bv 64 nw); C8 (Z_to_bv 64 0)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH Q QS Sop Swd Snn Bwn WT72.
      apply rw_cells_cons8_c; [lgc Hlf 2%nat ltac:(djd EF' ES'); first [apply WT72; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      apply rw_cells_cons8_c; [lgc Hlf 1%nat ltac:(djd EF' ES'); first [apply WT72; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      lgc Hlf 0%nat ltac:(djd EF' ES'); first [apply WT72; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1', ?L2', ?L8', ?L9', ?L10', ?L11', ?L12', ?L18', ?L19', ?L20', ?L21', ?L22', ?L23', ?L24', ?L25', ?L26', ?L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].  exact CC0.
  Qed.

End WoR4.

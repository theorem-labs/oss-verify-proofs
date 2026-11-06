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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_FKit LbA_WoR1 LbA_WoR2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition WO_MS1_RA : Z := 0xea294.
Definition WO_MS2_RA : Z := 0xea2a8.
Definition WO_MS3_RA : Z := 0xea2c0.
Definition WO_MS4_RA : Z := 0xea2d4.
Definition WO_MS5_RA : Z := 0xea2e8.
Definition WO_ON1_RA : Z := 0xea2f4.

Ltac djd EF' ES' := cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia.

Section WoR3.
  Context {HCEIL : HeapCeil}.

  Definition w2d_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff tenv lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS1_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (ff + 224)) (Z_to_bv 64 0) (Z_to_bv 64 32) x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
                    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 128, ff + 169); (S1 + 24, S1 + 48)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 128) [C4 (Z_to_bv 64 tenv)]
      /\ rw_cells asegs m1 (ff + 136) [C8 (Z_to_bv 64 (ff + 48)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C1 (b8 0)]
      /\ rw_cells asegs m1 (S1 + 24) [C8 (Z_to_bv 64 (ff + 32)); C8 (Z_to_bv 64 0x7fff8000); C8 (Z_to_bv 64 ff)].

  Lemma w2d : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff tenv lo : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) -> 0 <= tenv < 19 ->
    rw_cells asegs m (ff + 32) [C4 (Z_to_bv 64 tenv)] -> rw_cells asegs m (S1 + 56) [C8 (Z_to_bv 64 (ff + 48)); C8 (Z_to_bv 64 ff)] ->
    wr_at asegs m (ff + 128) 48 -> u8arr asegs m (sh ff) (map (Z_to_bv 8) WO_SH2C) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (w2d_post gp tp F fc SP S1 ff tenv lo m)
      (MS (mkR (Z_to_bv 64 WO_SM_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) x27 x28 x29 x30 x31) F (Z_to_bv 64 WO_PU) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP ENV CE CS WF US ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 WO_SM_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 tenv]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34);
                   (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880));
                   (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (20%bv, EMd M_MUL (ELit 64) (EVar 32));
                   (21%bv, ELit 2147450880); (22%bv, ELit 0); (23%bv, ELit 0); (24%bv, ELit 0); (25%bv, ELit 0);
                   (26%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 32))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      - transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]. rewrite QS, w_add by lia. f_equal. lia.
      - transitivity (Z_to_bv 64 (ff + 32)); [reflexivity|]. rewrite Q, w_add by lia. reflexivity. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 32) 4 (EVar 35);
        KWord (SA (EMd M_MUL (ELit 8) (EVar 32)) (SHBASE + 17)) 1 (ELit 0);
        KWord (SA (EVar 34) 56) 8 (EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 48));
        KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 128) (ELit 48);
        KWr (SA (EVar 34) 24) (ELit 24);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41); KRange (EVar 34) (2 ^ 45) (2 ^ 47);
        KRange (EVar 35) 0 18 ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 32) _ 0%nat (C4 (Z_to_bv 64 tenv))); [exact CE | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply (kword1_of_u8arr E m (sh ff) _ 17%nat); [exact US | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite ES'; unfold SHBASE; lia | lia | cbn; lia]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 56) _ 0%nat (C8 (Z_to_bv 64 (ff + 48)))); [exact CS | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; rewrite Q, w_add by lia; reflexivity]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_PU m (seg_rom asegs) HR HK 200%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24. rreg HR' 25%bv L25.
    rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    assert (L2' : getr R' 2 = Z_to_bv 64 S1) by (rewrite L2; reflexivity).
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by (rewrite L9; reflexivity).
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 224)) by (rewrite L10, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L19' : getr R' 19 = Z_to_bv 64 ff) by (rewrite L19; exact Q).
    assert (L20' : getr R' 20 = Z_to_bv 64 (ff + 176)) by (rewrite L20, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L26' : getr R' 26 = Z_to_bv 64 (ff + 32)) by (rewrite L26, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (MU1 : munch [(ff + 128, ff + 169); (S1 + 24, S1 + 48)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WSS : forall a n, S1 + 24 <= a -> a + n <= S1 + 48 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (WFF : forall a n, ff + 128 <= a -> a + n <= ff + 176 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WF as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 128 + (a - (ff + 128) + i)) by lia. apply W. lia. }
    assert (CP : rw_cells asegs M1 (ff + 128) [C4 (Z_to_bv 64 tenv)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH WFF Q.
      lgc Hlf 8%nat ltac:(djd EF' ES'). apply WFF; cbn; lia. }
    assert (CF : rw_cells asegs M1 (ff + 136) [C8 (Z_to_bv 64 (ff + 48)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C1 (b8 0)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH WFF Q.
      apply rw_cells_cons8_c; [lgc Hlf 4%nat ltac:(djd EF' ES'); [apply WFF; cbn; lia | HLib.evs; rewrite Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      apply rw_cells_cons8_c; [lgc Hlf 3%nat ltac:(djd EF' ES'); apply WFF; cbn; lia|].
      apply rw_cells_cons8_c; [lgc Hlf 2%nat ltac:(djd EF' ES'); apply WFF; cbn; lia|].
      apply rw_cells_cons8_c; [lgc Hlf 1%nat ltac:(djd EF' ES'); apply WFF; cbn; lia|].
      lgc Hlf 0%nat ltac:(djd EF' ES'). apply WFF; cbn; lia. }
    assert (CS2 : rw_cells asegs M1 (S1 + 24) [C8 (Z_to_bv 64 (ff + 32)); C8 (Z_to_bv 64 0x7fff8000); C8 (Z_to_bv 64 ff)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH FAPP S1L S1H SPH WSS Q.
      apply rw_cells_cons8_c; [lgc Hlf 7%nat ltac:(djd EF' ES'); [apply WSS; cbn; lia | HLib.evs; rewrite Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      apply rw_cells_cons8_c; [lgc Hlf 6%nat ltac:(djd EF' ES'); apply WSS; cbn; lia|].
      lgc Hlf 5%nat ltac:(djd EF' ES'); [apply WSS; cbn; lia | HLib.evs; rewrite Q; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2', L9', L10', L11, L12, L18', L19', L20', L21, L22, L23, L24, L25, L26', L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. split; [exact CP|]. split; [exact CF | exact CS2].
  Qed.

  Definition wr1_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS2_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 0) (Z_to_bv 64 46) x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
                    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 48, S1 + 56)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (S1 + 48) [C8 (Z_to_bv 64 (ff + 176))].

#[local] Definition HTLbAWoR3_0 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (20%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 176)); (21%bv, ELit 2147450880); (22%bv, ELit 0); (23%bv, ELit 0); (24%bv, ELit 0); (25%bv, ELit 0); (26%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 32)); (27%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 128))].
  Lemma wr1 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wr1_post gp tp F fc SP S1 ff lo m)
      (MS (mkR (Z_to_bv 64 WO_MS1_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS1_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S1L S1H SPH LO F64 FLO FS1 ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 WO_MS1_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR3_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD _ (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EVar 34) 48) (ELit 8);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS1_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24. rreg HR' 25%bv L25.
    rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    assert (L2' : getr R' 2 = Z_to_bv 64 S1) by (rewrite L2; reflexivity).
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by (rewrite L9; reflexivity).
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 176)) by (rewrite L10; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L19' : getr R' 19 = Z_to_bv 64 ff) by (rewrite L19; exact Q).
    assert (L20' : getr R' 20 = Z_to_bv 64 (ff + 176)) by (rewrite L20; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L26' : getr R' 26 = Z_to_bv 64 (ff + 32)) by (rewrite L26, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (MU1 : munch [(S1 + 48, S1 + 56)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WSS : forall a n, S1 + 48 <= a -> a + n <= S1 + 56 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (CC : rw_cells asegs M1 (S1 + 48) [C8 (Z_to_bv 64 (ff + 176))]).
    { subst M1. clear - Hlf EF' SHB SHL F64 FLO FS1 S1L S1H SPH WSS Q.
      lgc Hlf 0%nat ltac:(djd EF' EF'). all: first [apply WSS; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2', L9', L10', L11, L12, L18', L19', L20', L21, L22, L23, L24, L25, L26', L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST | exact CC].
  Qed.

  Definition wr2_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS3_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (ff + 264)) (Z_to_bv 64 0) (Z_to_bv 64 32) x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
                    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 256, ff + 260)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 256) [C4 (Z_to_bv 64 0x3f800000)].

  Lemma wr2 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> wr_at asegs m (ff + 256) 4 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wr2_post gp tp F fc SP S1 ff lo m)
      (MS (mkR (Z_to_bv 64 WO_MS2_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS2_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S1L S1H SPH LO F64 FLO FS1 WF ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 WO_MS2_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR3_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD _ (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 256) (ELit 4);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS2_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24. rreg HR' 25%bv L25.
    rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    assert (L2' : getr R' 2 = Z_to_bv 64 S1) by (rewrite L2; reflexivity).
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by (rewrite L9; reflexivity).
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 264)) by (rewrite L10; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L19' : getr R' 19 = Z_to_bv 64 ff) by (rewrite L19; exact Q).
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L26' : getr R' 26 = Z_to_bv 64 (ff + 32)) by (rewrite L26, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (MU1 : munch [(ff + 256, ff + 260)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WSS : forall a n, ff + 256 <= a -> a + n <= ff + 260 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WF as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 256 + (a - (ff + 256) + i)) by lia. apply W. lia. }
    assert (CC : rw_cells asegs M1 (ff + 256) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. clear - Hlf EF' SHB SHL F64 FLO FS1 S1L S1H SPH WSS Q.
      lgc Hlf 0%nat ltac:(djd EF' EF'). all: first [apply WSS; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2', L9', L10', L11, L12, L18', L19', L20', L21, L22, L23, L24, L25, L26', L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST | exact CC].
  Qed.

  Definition wr3_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS4_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (ff + 304)) (Z_to_bv 64 0) (Z_to_bv 64 32) x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
                    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 296, ff + 300)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 296) [C4 (Z_to_bv 64 0x3f800000)].

#[local] Definition HTLbAWoR3_1 : list (reg * expr) := [(2%bv, EVar 34); (9%bv, EVar 34); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (19%bv, EMd M_MUL (ELit 64) (EVar 32)); (20%bv, ELit 1065353216); (21%bv, ELit 2147450880); (22%bv, ELit 0); (23%bv, ELit 0); (24%bv, ELit 0); (25%bv, ELit 0); (26%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 32)); (27%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 128))].
  Lemma wr3 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> wr_at asegs m (ff + 296) 4 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wr3_post gp tp F fc SP S1 ff lo m)
      (MS (mkR (Z_to_bv 64 WO_MS3_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS3_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S1L S1H SPH LO F64 FLO FS1 WF ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 WO_MS3_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR3_1) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD _ (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 296) (ELit 4);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS3_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24. rreg HR' 25%bv L25.
    rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    assert (L2' : getr R' 2 = Z_to_bv 64 S1) by (rewrite L2; reflexivity).
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by (rewrite L9; reflexivity).
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 304)) by (rewrite L10; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L19' : getr R' 19 = Z_to_bv 64 ff) by (rewrite L19; exact Q).
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L26' : getr R' 26 = Z_to_bv 64 (ff + 32)) by (rewrite L26, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (MU1 : munch [(ff + 296, ff + 300)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WSS : forall a n, ff + 296 <= a -> a + n <= ff + 300 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WF as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 296 + (a - (ff + 296) + i)) by lia. apply W. lia. }
    assert (CC : rw_cells asegs M1 (ff + 296) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. clear - Hlf EF' SHB SHL F64 FLO FS1 S1L S1H SPH WSS Q.
      lgc Hlf 0%nat ltac:(djd EF' EF'). all: first [apply WSS; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2', L9', L10', L11, L12, L18', L19', L20', L21, L22, L23, L24, L25, L26', L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST | exact CC].
  Qed.

  Definition wr4_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS5_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (ff + 344)) (Z_to_bv 64 0) (Z_to_bv 64 72) x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
                    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 336, ff + 340)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 336) [C4 (Z_to_bv 64 0x3f800000)].

  Lemma wr4 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> wr_at asegs m (ff + 336) 4 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wr4_post gp tp F fc SP S1 ff lo m)
      (MS (mkR (Z_to_bv 64 WO_MS4_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS4_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S1L S1H SPH LO F64 FLO FS1 WF ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 WO_MS4_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR3_1) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD _ (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 336) (ELit 4);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS4_RA m (seg_rom asegs) HR HK 60%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24. rreg HR' 25%bv L25.
    rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    assert (L2' : getr R' 2 = Z_to_bv 64 S1) by (rewrite L2; reflexivity).
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by (rewrite L9; reflexivity).
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 344)) by (rewrite L10; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L18' : getr R' 18 = Z_to_bv 64 (sh ff)) by (rewrite L18, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L19' : getr R' 19 = Z_to_bv 64 ff) by (rewrite L19; exact Q).
    assert (L20' : getr R' 20 = Z_to_bv 64 (0x3f800000)) by (rewrite L20; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L26' : getr R' 26 = Z_to_bv 64 (ff + 32)) by (rewrite L26, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 128)) by (rewrite L27, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (MU1 : munch [(ff + 336, ff + 340)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WSS : forall a n, ff + 336 <= a -> a + n <= ff + 340 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WF as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 336 + (a - (ff + 336) + i)) by lia. apply W. lia. }
    assert (CC : rw_cells asegs M1 (ff + 336) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. clear - Hlf EF' SHB SHL F64 FLO FS1 S1L S1H SPH WSS Q.
      lgc Hlf 0%nat ltac:(djd EF' EF'). all: first [apply WSS; cbn; lia | HLib.evs; rewrite ?Q, ?w_add, ?v_addi_Z by lia; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2', L9', L10', L11, L12, L18', L19', L20', L21, L22, L23, L24, L25, L26', L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST | exact CC].
  Qed.

  Definition wr5_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 (WO_ON1_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (500)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (0x7fff8000)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wr5 : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo : Z),
    2 ^ 45 <= S1 -> S1 + 416 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 512 <= S1 -> (sh ff + 64 <= ff \/ ff + 512 <= sh ff) ->
    (ff + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    rw_cells asegs m (ff + 352) [CB 8 (poison_bytes 8 0)] ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wr5_post gp tp F fc SP S1 ff lo m)
      (MS (mkR (Z_to_bv 64 (WO_MS5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (ff + 344)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (0x7fff8000)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) F (Z_to_bv 64 WO_MS5_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo. intros S1L S1H SPH LO F64 FLO FS1 FSH FAPP Z8 ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR (Z_to_bv 64 (WO_MS5_RA)) (Z_to_bv 64 (S1)) gp tp x5 x6 x7 (Z_to_bv 64 (SP)) (Z_to_bv 64 (S1)) (Z_to_bv 64 (ff + 344)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (ff)) (Z_to_bv 64 (0x3f800000)) (Z_to_bv 64 (0x7fff8000)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (0)) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id HTLbAWoR3_1) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end
                 | match goal with |- getr _ _ = alu64 ALU_ADD (Z_to_bv 64 _) (Z_to_bv 64 ?k) =>
                     rewrite w_add by lia; reflexivity end ]. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 352) 8 (ELit 0);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 352) _ 0%nat (CB 8 (poison_bytes 8 0))); [exact Z8 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | vm_compute; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS5_RA m (seg_rom asegs) HR HK 40%nat [AOPNEW] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = Z_to_bv 64 (WO_ON1_RA)) by (rewrite L1; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
    assert (L21' : getr R' 21 = Z_to_bv 64 (0x7fff8000)) by (rewrite L21; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 22%bv L22.
    assert (L22' : getr R' 22 = Z_to_bv 64 (0)) by (rewrite L22; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 23%bv L23.
    assert (L23' : getr R' 23 = Z_to_bv 64 (0)) by (rewrite L23; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 24%bv L24.
    assert (L24' : getr R' 24 = Z_to_bv 64 (0)) by (rewrite L24; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 25%bv L25.
    assert (L25' : getr R' 25 = Z_to_bv 64 (0)) by (rewrite L25; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
    rreg HR' 26%bv L26.
    assert (L26' : getr R' 26 = Z_to_bv 64 (ff + 32)) by (rewrite L26; first [reflexivity | rewrite HR0; reflexivity | rewrite ?Q, ?QS, ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]]).
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
End WoR3.

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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_RGb1 LbA_RGb2 LbA_RG2 LbA_Ctx LbA_TopH1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition TOP_F8_RA : Z := 0xe8d48.
Definition TOP_00_RA : Z := 0xe8dd4.
Definition TOP_RET6 : Z := 0xe8f84.
Definition TOP_RG_RA : Z := 0xe8de4.
Definition TOP_GTE_RA : Z := 0xe8dec.
Definition TOP_CTX_RA : Z := 0xe8df0.

Lemma sh_q : forall ff, 0 <= ff < 2 ^ 47 -> ff mod 64 = 0 ->
  mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000).
Proof.
  intros ff H1 H2. rewrite w_mul by (Z.div_mod_to_equations; lia). f_equal.
  unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
Qed.

Section TopH2.
  Context {HCEIL : HeapCeil}.

  Definition h2a_post (gp tp s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff D N lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 313) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N) s7 s8
                    (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 ASET_SHADOW_F8) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 16, S1 + 24); (ff, ff + 24); (sh ff, sh ff + 4)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo SP.

  Lemma h2a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s7 s8 s9 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff D N lo : Z),
    S1 mod 32 = 0 -> 2 ^ 45 <= S1 -> S1 + 128 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 <= ff -> ff + 4096 <= 2 ^ 47 ->
    wr_at asegs m ff 24 -> wr_at asegs m (sh ff) 4 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (h2a_post gp tp s7 s8 s11 F fc SP S1 ff D N lo m)
      (MS (mkR (Z_to_bv 64 TOP_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 ff)
               x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 (Z_to_bv 64 D) (Z_to_bv 64 N) s7 s8 s9 (Z_to_bv 64 0x7fff8000) s11
               x28 x29 x30 x31) F (Z_to_bv 64 TOP_SM_RET) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S32 S1L S1H SPH LO F64 FLO FHI WF WS ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000)
      by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHQ : 8 * (ff / 64) = sh ff - 0x7fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    remember (mkR (Z_to_bv 64 TOP_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 ff)
               x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 (Z_to_bv 64 D) (Z_to_bv 64 N) s7 s8 s9 (Z_to_bv 64 0x7fff8000) s11
               x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EMd M_MUL (ELit 64) (EVar 32)); (9%bv, EVar 33); (26%bv, ELit 2147450880)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity. rewrite Q. reflexivity. }
    assert (EF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 32))) = ff) by (evs; rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = sh ff - 0x7fff8000)
      by (evs; rewrite QS, u64_of_Z by lia; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 33)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
       [ KWr (SA (EVar 33) 16) (ELit 8);
         KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 24);
         KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 4);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) (0x6e6000 / 64) (2 ^ 41) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite EP; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EP; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EF; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EF; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; unfold SHBASE; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_SM_RET m (seg_rom asegs) HR HK 100%nat [ASET_SHADOW_F8] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 18%bv L18. rreg HR' 19%bv L19.
    rreg HR' 20%bv L20. rreg HR' 25%bv L25. rreg HR' 26%bv L26.
    assert (L10' : getr R' 10 = Z_to_bv 64 (sh ff + 4)) by (rewrite L10, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L20' : getr R' 20 = Z_to_bv 64 (sh ff + 4)) by (rewrite L20, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L19' : getr R' 19 = Z_to_bv 64 (sh ff)) by (rewrite L19, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L18' : getr R' 18 = Z_to_bv 64 ff) by (rewrite L18; exact Q).
    assert (L25' : getr R' 25 = Z_to_bv 64 ff) by (rewrite L25; exact Q).
    assert (MU1 : munch [(S1 + 16, S1 + 24); (ff, ff + 24); (sh ff, sh ff + 4)] m M1).
    { subst M1. clear - Hlf S32 S1L S1H SPH F64 FLO FHI SHL SHQ Q QS. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?Q, ?QS; rewrite ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; unfold SHBASE; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L9, L10', L11, L18', L19', L20', L25', L26.
    apply evt_done.
    do 14 eexists; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition h3a_post (gp tp s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff D N lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 TOP_00_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 313) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N) (Z_to_bv 64 (ff + 32)) s8
                    (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 ASET_SHADOW_00) fc None m1 (seg_rom asegs)
      /\ munch [(sh ff + 317, sh ff + 344)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.

  Lemma h3a : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s7 s8 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff D N lo : Z),
    1 <= N < 2 ^ 26 -> 0 <= S1 <= 2 ^ 47 -> 0 <= SP <= 2 ^ 47 -> 0 <= D < 2 ^ 64 ->
    ff mod 64 = 0 -> 0x6e6000 <= ff -> ff + 4096 <= 2 ^ 47 ->
    wr_at asegs m (sh ff + 317) 27 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (h3a_post gp tp s8 s11 F fc SP S1 ff D N lo m)
      (MS (mkR (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N)
               s7 s8 (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 TOP_F8_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros HN S1R SPR DR F64 FLO FHI WS ST MI.
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000)
      by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    remember (mkR (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N)
               s7 s8 (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (sh ff); Z_to_bv 64 N; Z_to_bv 64 ff; Z_to_bv 64 (sh ff + 4)]).
    assert (HR : regs_ok E (srs sr_id [(19%bv, EVar 32); (22%bv, EVar 33); (25%bv, EVar 34); (20%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        reflexivity. }
    assert (ES : bv_unsigned (edenot E (EVar 32)) = sh ff) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWr (SA (EVar 32) 317) (ELit 27); KRange (EVar 33) 1 (2 ^ 26); KRange (EVar 32) 0 (2 ^ 45) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite ES. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_F8_RA m (seg_rom asegs) HR HK 100%nat [ASET_SHADOW_00; TOP_RET6] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 25%bv L25.
    assert (L23' : getr R' 23 = Z_to_bv 64 (ff + 32)) by (rewrite L23; rewrite ?w_add, ?w_addm by lia; f_equal).
    assert (MU1 : munch [(sh ff + 317, sh ff + 344)] m M1).
    { subst M1. clear - Hlf SHL. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L10, L11, L19, L20, L22, L23', L25.
    apply evt_done.
    do 14 eexists; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition h3z_post (gp tp s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff D lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 0) s7 s8
                    (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 TOP_RET6) fc None m1 (seg_rom asegs)
      /\ munch [(sh ff + 317, sh ff + 344)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.

  Lemma h3z : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s7 s8 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff D lo : Z),
    0 <= S1 <= 2 ^ 47 -> 0 <= SP <= 2 ^ 47 -> 0 <= D < 2 ^ 64 ->
    ff mod 64 = 0 -> 0x6e6000 <= ff -> ff + 4096 <= 2 ^ 47 ->
    wr_at asegs m (sh ff + 317) 27 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (h3z_post gp tp s7 s8 s11 F fc SP S1 ff D lo m)
      (MS (mkR (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 0)
               s7 s8 (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 TOP_F8_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S1R SPR DR F64 FLO FHI WS ST MI.
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000)
      by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    remember (mkR (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 0)
               s7 s8 (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (sh ff)]).
    assert (HR : regs_ok E (srs sr_id [(19%bv, EVar 32); (22%bv, ELit 0)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        reflexivity. }
    assert (ES : bv_unsigned (edenot E (EVar 32)) = sh ff) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWr (SA (EVar 32) 317) (ELit 27); KRange (EVar 32) 0 (2 ^ 45) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite ES. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_F8_RA m (seg_rom asegs) HR HK 100%nat [ASET_SHADOW_00; TOP_RET6] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 19%bv L19. rreg HR' 22%bv L22.
    assert (MU1 : munch [(sh ff + 317, sh ff + 344)] m M1).
    { subst M1. clear - Hlf SHL. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L19, L22.
    apply evt_done.
    do 17 eexists; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Lemma h4a : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s8 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff D N : Z),
    0 <= ff < 2 ^ 47 ->
    evt asegs (fun ms' => exists x13' x14' x15' x16' x17',
        ms' = MS (mkR (Z_to_bv 64 TOP_RG_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                      (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 D) (Z_to_bv 64 N) x13' x14' x15' x16' x17'
                      (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N) (Z_to_bv 64 (ff + 32)) s8
                      (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 RG_CTOR) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 TOP_00_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N)
               (Z_to_bv 64 (ff + 32)) s8 (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 TOP_00_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until N. intros FR.
    remember (mkR (Z_to_bv 64 TOP_00_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N)
               (Z_to_bv 64 (ff + 32)) s8 (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R []).
    assert (HR : regs_ok E (srs sr_id []) R) by (apply regs_ok_srs; [apply regs_ok_seed| apply Forall_nil]).
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R TOP_00_RA m (seg_rom asegs) HR HK 20%nat [RG_CTOR] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L10, L11, L12. subst R. cbn [getr mkR].
    apply evt_done. cbn [mem_denot]. do 5 eexists. reflexivity.
  Qed.

  Lemma h5a : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s8 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff D N : Z),
    evt asegs (fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 TOP_GTE_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                      (Z_to_bv 64 (ff + 32)) x11 x12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N) (Z_to_bv 64 (ff + 32)) s8
                      (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 GTE_ENTRY) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 TOP_RG_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N)
               (Z_to_bv 64 (ff + 32)) s8 (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 TOP_RG_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until N.
    remember (mkR (Z_to_bv 64 TOP_RG_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N)
               (Z_to_bv 64 (ff + 32)) s8 (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R []).
    assert (HR : regs_ok E (srs sr_id []) R) by (apply regs_ok_srs; [apply regs_ok_seed| apply Forall_nil]).
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R TOP_RG_RA m (seg_rom asegs) HR HK 20%nat [GTE_ENTRY] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L10. subst R. cbn [getr mkR].
    apply evt_done. cbn [mem_denot]. reflexivity.
  Qed.

  Lemma h6a : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s8 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff D N : Z),
    evt asegs (fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 TOP_CTX_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                      x10 x11 x12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N) (Z_to_bv 64 (ff + 32)) s8
                      (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 CTX_CREATE) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 TOP_GTE_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N)
               (Z_to_bv 64 (ff + 32)) s8 (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 TOP_GTE_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until N.
    remember (mkR (Z_to_bv 64 TOP_GTE_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N)
               (Z_to_bv 64 (ff + 32)) s8 (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R []).
    assert (HR : regs_ok E (srs sr_id []) R) by (apply regs_ok_srs; [apply regs_ok_seed| apply Forall_nil]).
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R TOP_GTE_RA m (seg_rom asegs) HR HK 20%nat [CTX_CREATE] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1. subst R. cbn [getr mkR].
    apply evt_done. cbn [mem_denot]. reflexivity.
  Qed.
End TopH2.

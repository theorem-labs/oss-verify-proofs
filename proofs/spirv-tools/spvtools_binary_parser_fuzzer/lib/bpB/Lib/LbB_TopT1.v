(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_TopH2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition TOP_SF_RA : Z := 0xe8c74.
Definition TOP_RET : Z := 0xe8cc4.

Section TopT1.
  Context {HCEIL : HeapCeil}.

  Lemma hT1 : forall (x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo : Z),
    0x6e6000 <= ff -> ff + 4096 <= 2 ^ 47 ->
    wr_at asegs m ff 8 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (fun ms' => exists m1,
        ms' = MS (mkR (Z_to_bv 64 TOP_SF_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) x9 (Z_to_bv 64 ff) (Z_to_bv 64 2752)
                      x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) x19 (Z_to_bv 64 ff) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 AFS_FREE_6) fc None m1 (seg_rom asegs)
        /\ munch [(ff, ff + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP)
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ff) x19 (Z_to_bv 64 ff) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 TOP_RET6) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros FLO FHI WF ST MI.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ff) x19 (Z_to_bv 64 ff) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(18%bv, EVar 32); (20%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (EF : bv_unsigned (edenot E (EVar 32)) = ff) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWr (SA (EVar 32) 0) (ELit 8); KRange (EVar 32) 1 (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EF; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EF; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EF. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_RET6 m (seg_rom asegs) HR HK 40%nat [AFS_FREE_6] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 18%bv L18. rreg HR' 20%bv L20.
    assert (MU1 : munch [(ff, ff + 8)] m M1).
    { subst M1. clear - Hlf FLO FHI. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L10, L11, L18, L20.
    apply evt_done.
    exists M1. split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Lemma hT2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP : Z),
    s0 = Z_to_bv 64 SP -> 2 ^ 45 <= SP <= 2 ^ 47 ->
    rw_cells asegs m (SP - 104) [C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra'] ->
    evt asegs (fun ms' =>
        ms' = MS (mkR ra' (Z_to_bv 64 SP) gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                      s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6) F (ret_pc ra') fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 TOP_SF_RA) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TOP_SF_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until SP. intros Hs0 SPR CS.
    remember (mkR (Z_to_bv 64 TOP_SF_RA) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 SP; s11'; s10'; s9'; s8'; s7'; s6'; s5'; s4'; s3'; s2'; s1'; s0'; ra']).
    assert (HR : regs_ok E (srs sr_id [(8%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; exact Hs0. }
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 32) (-104)) 8 (EVar 33); KWord (SA (EVar 32) (-96)) 8 (EVar 34); KWord (SA (EVar 32) (-88)) 8 (EVar 35);
         KWord (SA (EVar 32) (-80)) 8 (EVar 36); KWord (SA (EVar 32) (-72)) 8 (EVar 37); KWord (SA (EVar 32) (-64)) 8 (EVar 38);
         KWord (SA (EVar 32) (-56)) 8 (EVar 39); KWord (SA (EVar 32) (-48)) 8 (EVar 40); KWord (SA (EVar 32) (-40)) 8 (EVar 41);
         KWord (SA (EVar 32) (-32)) 8 (EVar 42); KWord (SA (EVar 32) (-24)) 8 (EVar 43); KWord (SA (EVar 32) (-16)) 8 (EVar 44);
         KWord (SA (EVar 32) (-8)) 8 (EVar 45);
         KRange (EVar 32) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { kword_cell CS 0%nat (C8 s11'). }
      apply Forall_cons. { kword_cell CS 8%nat (C8 s10'). }
      apply Forall_cons. { kword_cell CS 16%nat (C8 s9'). }
      apply Forall_cons. { kword_cell CS 24%nat (C8 s8'). }
      apply Forall_cons. { kword_cell CS 32%nat (C8 s7'). }
      apply Forall_cons. { kword_cell CS 40%nat (C8 s6'). }
      apply Forall_cons. { kword_cell CS 48%nat (C8 s5'). }
      apply Forall_cons. { kword_cell CS 56%nat (C8 s4'). }
      apply Forall_cons. { kword_cell CS 64%nat (C8 s3'). }
      apply Forall_cons. { kword_cell CS 72%nat (C8 s2'). }
      apply Forall_cons. { kword_cell CS 80%nat (C8 s1'). }
      apply Forall_cons. { kword_cell CS 88%nat (C8 s0'). }
      apply Forall_cons. { kword_cell CS 96%nat (C8 ra'). }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_SF_RA m (seg_rom asegs) HR HK 40%nat [TOP_RET] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 18%bv L18.
    rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24.
    rreg HR' 25%bv L25. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    assert (L2' : getr R' 2 = Z_to_bv 64 SP) by (rewrite L2; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2', L8, L9, L10, L18, L19, L20, L21, L22, L23, L24, L25, L26, L27.
    cbn [mem_denot]. unfold TOP_RET. step.
    apply evt_done. reflexivity.
  Qed.

  Lemma hE1 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo : Z),
    0x6e8000 + 0x9000 <= ff -> ff + 4096 <= 2 ^ 47 -> ff mod 64 = 0 -> 2 ^ 45 <= S1 -> S1 + 64 <= 2 ^ 47 ->
    rw_cells asegs m (S1 + 32) [C8 (wz (sh ff + 4)); C8 (wz ff); C8 (wz (sh ff)); C8 (wz ff)] ->
    wr_at asegs m (sh ff + 334) 3 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (fun ms' => exists m1,
        ms' = MS (mkR (Z_to_bv 64 TOP_RET6) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 (sh ff + 4))
                      (Z_to_bv 64 313) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff)
                      (Z_to_bv 64 (sh ff)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 ASET_SHADOW_F8) fc None m1 (seg_rom asegs)
        /\ munch [(sh ff + 334, sh ff + 337)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP)
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8c28) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros FLO FHI F64 S1L S1H CF WS ST MI.
    assert (QB : 0 <= ff / 64 < 2 ^ 41) by (Z.div_mod_to_equations; lia).
    assert (QD : ff = 64 * (ff / 64)) by (pose proof (Z.div_mod ff 64 ltac:(lia)); lia).
    assert (SHQ : sh ff = 8 * (ff / 64) + 2147450880) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (EQ8 : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (8 * (ff / 64))) by (apply w_mul; lia).
    assert (EQ64 : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (rewrite w_mul by lia; f_equal; lia).
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 S1]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (9%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (ES : bv_unsigned (edenot E (EVar 33)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (EQ : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = 8 * (ff / 64)) by (evs; rewrite EQ8, u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 33) 32) 8 (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450884));
         KWord (SA (EVar 33) 40) 8 (EMd M_MUL (ELit 64) (EVar 32));
         KWord (SA (EVar 33) 48) 8 (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880));
         KWord (SA (EVar 33) 56) 8 (EMd M_MUL (ELit 64) (EVar 32));
         KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) 2147451214) (ELit 3);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0 (2 ^ 41) ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 0%nat (C8 (wz (sh ff + 4)))); [exact CF | reflexivity | reflexivity | lia
          | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
        cbn [cbytes edenot]. evs. rewrite EQ8, w_add by lia. unfold wz. replace (8 * (ff / 64) + 2147450884) with (sh ff + 4) by lia. reflexivity. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 8%nat (C8 (wz ff))); [exact CF | reflexivity | reflexivity | lia
          | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
        cbn [cbytes edenot]. evs. rewrite EQ64. reflexivity. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 16%nat (C8 (wz (sh ff)))); [exact CF | reflexivity | reflexivity | lia
          | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
        cbn [cbytes edenot]. evs. rewrite EQ8, w_add by lia. unfold wz. replace (8 * (ff / 64) + 2147450880) with (sh ff) by lia. reflexivity. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 24%nat (C8 (wz ff))); [exact CF | reflexivity | reflexivity | lia
          | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
        cbn [cbytes edenot]. evs. rewrite EQ64. reflexivity. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite EQ; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EQ; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite ES. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xe8c28 m (seg_rom asegs) HR HK 40%nat [ASET_SHADOW_F8] (SCR [] [] []) 50%N.
    { split_scs; cbn [sc_denot]; unfold flat; evs; rewrite ?u64_of_Z by lia; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21.
    rewrite EQ8, w_add in L10, L19, L21 by lia. rewrite EQ64 in L18, L20.
    replace (8 * (ff / 64) + 2147450884) with (sh ff + 4) in L10, L19 by lia.
    replace (8 * (ff / 64) + 2147450880) with (sh ff) in L21 by lia.
    assert (MU1 : munch [(sh ff + 334, sh ff + 337)] m M1).
    { subst M1. clear - Hlf EQ8 QB SHQ. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?EQ8, ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L9, L10, L11, L18, L19, L20, L21.
    apply evt_done.
    exists M1. split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Lemma hVD1 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 V lo : Z),
    2 ^ 45 <= S1 -> S1 + 128 <= SP <= 2 ^ 47 -> 0 <= V < 2 ^ 64 ->
    rw_cells asegs m (S1 + 80) [C8 (wz V)] -> stk asegs m lo SP -> lo <= S1 -> mem_inv asegs m ->
    evt asegs (fun ms' => exists m1,
        ms' = MS (mkR (Z_to_bv 64 0xe8c28) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 112))
                      x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 0xe8e94) fc None m1 (seg_rom asegs)
        /\ munch [(S1 + 112, S1 + 120)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
        /\ rw_cells asegs m1 (S1 + 112) [C8 (Z_to_bv 64 V)])
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8c18) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S1L S1H VR CVf ST LO MI.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 V]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (EP : bv_unsigned (edenot E (EVar 32)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (WS : wr_at asegs m (S1 + 112) 8).
    { pose proof (wr_at_of_stk asegs m lo SP ST) as (W1 & W2 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (S1 + 112 + i) with (lo + (S1 + 112 - lo + i)) by lia. apply W. lia. }
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 80) 8 (EVar 33); KWr (SA (EVar 32) 112) (ELit 8); KRange (EVar 32) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { kword_cell CVf 0%nat (C8 (wz V)). }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite EP; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EP; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xe8c18 m (seg_rom asegs) HR HK 20%nat [0xe8e94] (SCR [] [] []) 50%N.
    { split_scs; cbn [sc_denot]; unfold flat; evs; rewrite ?u64_of_Z by lia; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (CV0 : rw_cells asegs M1 (S1 + 112) [C8 (edenot E (EVar 33))]).
    { subst M1. eapply (rw_cells_mem_denot_C8 E m [] _ _ []); [exact Hlf | apply Forall_nil | unfold estart; cbn [a_base a_off]; rewrite EP; lia | exact WS]. }
    assert (EV : edenot E (EVar 33) = Z_to_bv 64 V) by (evs; reflexivity).
    assert (CV : rw_cells asegs M1 (S1 + 112) [C8 (Z_to_bv 64 V)]) by (rewrite <- EV; exact CV0).
    clear CV0.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 9%bv L9. rreg HR' 10%bv L10.
    assert (L10' : getr R' 10 = Z_to_bv 64 (S1 + 112)) by (rewrite L10; rewrite ?w_add, ?w_addm by lia; f_equal).
    assert (MU1 : munch [(S1 + 112, S1 + 120)] m M1).
    { subst M1. clear - Hlf S1L S1H. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L9, L10'.
    apply evt_done.
    exists M1. split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST | exact CV].
  Qed.

  Lemma hCD1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    evt asegs (fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 0xe8c18) x2 x3 x4 x5 x6 x7 x8 x9 x18 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                      x28 x29 x30 x31) F (Z_to_bv 64 0xea008) fc None m (seg_rom asegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8c10) fc None m (seg_rom asegs)).
  Proof.
    intros.
    remember (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R []).
    assert (HR : regs_ok E (srs sr_id []) R) by (apply regs_ok_srs; [apply regs_ok_seed| apply Forall_nil]).
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R 0xe8c10 m (seg_rom asegs) HR HK 20%nat [0xea008] (SCR [] [] []) 40%N.
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
End TopT1.

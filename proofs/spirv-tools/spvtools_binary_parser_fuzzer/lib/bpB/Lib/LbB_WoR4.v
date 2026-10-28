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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX BArr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_FKit LbB_WoR2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition WO_AN1_RA : Z := 0xeb324.
Definition WO_AN2_RA : Z := 0xeb330.
Definition WO_AN3_RA : Z := 0xeb33c.
Definition WO_MS6_RA : Z := 0xeb3f0.

Definition WO_SH4T : list Z :=
  repeat 0xf1 4 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++ repeat 0xf2 5 ++ repeat 0xf8 3 ++
  repeat 0xf2 5 ++ repeat 0xf8 50 ++ repeat 0xf2 8 ++ repeat 0xf8 50 ++ repeat 0xf2 8 ++ repeat 0xf8 2 ++
  repeat 0xf2 2 ++ repeat 0xf8 50 ++ repeat 0xf2 8 ++ repeat 0xf8 4 ++ repeat 0xf2 4 ++ repeat 0xf8 50 ++
  repeat 0xf2 8 ++ repeat 0 30 ++ repeat 0xf2 8 ++ repeat 0xf8 30 ++ repeat 0xf2 8 ++ repeat 0 8 ++ repeat 0xf2 4 ++
  repeat 0 36 ++ repeat 0xf3 8.

Section WoR4.
  Context {HCEIL : HeapCeil}.

  Definition we1c_post (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
    fun ms' => ms' = MS (mkR (Z_to_bv 64 WO_AN2_RA) sp gp tp t0 t1 t2 s0 s1 s10 (Z_to_bv 64 25) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xec634) fc None m (seg_rom asegs).
  Lemma we1c : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    evt asegs (we1c_post sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 WO_AN1_RA) fc None m (seg_rom asegs)).
  Proof.
    intros. remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R []).
    assert (HR : regs_ok E (srs sr_id []) R) by (apply regs_ok_srs; [apply regs_ok_seed | constructor]).
    assert (HK : know_ok asegs E m []) by (unfold know_ok; apply Forall_nil).
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN1_RA m (seg_rom asegs) HR HK 10%nat [0xec634] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    assert (L10' : getr R' 10 = s10) by (rewrite L10; subst R; reflexivity).
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L10', L11.
    apply evt_done. reflexivity.
  Qed.

  Definition we2c_post (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
    fun ms' => ms' = MS (mkR (Z_to_bv 64 WO_AN3_RA) sp gp tp t0 t1 t2 s0 s1 s5 (Z_to_bv 64 25) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xec788) fc None m (seg_rom asegs).
  Lemma we2c : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    evt asegs (we2c_post sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 WO_AN2_RA) fc None m (seg_rom asegs)).
  Proof.
    intros. remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R []).
    assert (HR : regs_ok E (srs sr_id []) R) by (apply regs_ok_srs; [apply regs_ok_seed | constructor]).
    assert (HK : know_ok asegs E m []) by (unfold know_ok; apply Forall_nil).
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN2_RA m (seg_rom asegs) HR HK 10%nat [0xec788] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    assert (L10' : getr R' 10 = s5) by (rewrite L10; subst R; reflexivity).
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L10', L11.
    apply evt_done. reflexivity.
  Qed.

  Definition we3c_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo words nw : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS6_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (ff + 2776)) (Z_to_bv 64 0) (Z_to_bv 64 22) x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 2800)) (Z_to_bv 64 (ff + 3504))
                    (Z_to_bv 64 0x3f800000) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 (ff + 3696)) (Z_to_bv 64 (ff + 2752))
                    x28 x29 x30 x31) F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(sh ff + 344, sh ff + 374); (ff + 2752, ff + 2776)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 2752) [C8 (Z_to_bv 64 words); C8 (Z_to_bv 64 nw); C8 (Z_to_bv 64 0)]
      /\ u8arr asegs m1 (sh ff) (map (Z_to_bv 8) WO_SH4T).
  Lemma we3c : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (SP S1 ff lo words nw : Z),
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 + 0x9000 <= ff -> ff + 3808 <= S1 -> (sh ff + 476 <= ff \/ ff + 3808 <= sh ff) ->
    rw_cells asegs m (S1 + 16) [C8 (Z_to_bv 64 0)] ->
    rw_cells asegs m (S1 + 24) [C8 (Z_to_bv 64 words)] ->
    rw_cells asegs m (S1 + 32) [C8 (Z_to_bv 64 nw)] ->
    0 <= words < 2 ^ 64 /\ 0 <= nw < 2 ^ 64 ->
    wr_at asegs m (ff + 2752) 24 -> u8arr asegs m (sh ff) (map (Z_to_bv 8) WO_SH2C) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we3c_post gp tp F fc SP S1 ff lo words nw m)
      (MS (mkR (Z_to_bv 64 WO_AN3_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3720)) (Z_to_bv 64 (ff + 3504))
               (Z_to_bv 64 0x3f800000) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 (ff + 3696)) (Z_to_bv 64 (ff + 2752))
               x28 x29 x30 x31) F (Z_to_bv 64 WO_AN3_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m SP S1 ff lo words nw.
    intros S1L S1H SPH LO F64 FLO FS1 FSH Sfl Swd Snn Bwn WT US ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 476 <= 2 ^ 45)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    assert (WS : wr_at asegs m (sh ff) 476).
    { destruct US as (_ & (W1 & W2 & W)). rewrite length_map in W2, W. cbn [length WO_SH2C app repeat] in W2, W.
      split; [lia|]. split; [lia|]. intros i Hi. apply W. cbn. lia. }
    assert (WT' : forall a n, ff + 2752 <= a -> a + n <= ff + 2776 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WT as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 2752 + (a - (ff + 2752) + i)) by lia. apply W. lia. }
    remember (mkR (Z_to_bv 64 WO_AN3_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3720)) (Z_to_bv 64 (ff + 3504))
               (Z_to_bv 64 0x3f800000) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 (ff + 3696)) (Z_to_bv 64 (ff + 2752))
               x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 words; Z_to_bv 64 nw]).
    assert (HR : regs_ok E (srs sr_id [(9%bv, EVar 34);
                   (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 3456));
                   (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880));
                   (20%bv, EMd M_MUL (ELit 64) (EVar 32)); (24%bv, ELit 0);
                   (27%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 2752))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      all: first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
                 | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
                     transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end ]. }
    assert (ESb : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = sh ff - 0x7fff8000)
      by (evs; rewrite QS, u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
      [ KWord (SA (EVar 34) 16) 8 (ELit 0);
        KWord (SA (EVar 34) 24) 8 (EVar 36);
        KWord (SA (EVar 34) 32) 8 (EVar 37);
        KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 2752) (ELit 24);
        KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) (SHBASE + 344)) (ELit 30);
        KRange (EVar 32) ((0x6e6000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 16) _ 0%nat (C8 (Z_to_bv 64 0))); [exact Sfl | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 24) _ 0%nat (C8 (Z_to_bv 64 words))); [exact Swd | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 32) _ 0%nat (C8 (Z_to_bv 64 nw))); [exact Snn | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WT | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; evs; rewrite ES'; unfold SHBASE; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite ES', u64_of_Z by lia; unfold SHBASE; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN3_RA m (seg_rom asegs) HR HK 100%nat [AASAN_MEMSET] (SCR [] [] []) 60%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 24%bv L24. rreg HR' 27%bv L27.
    assert (L1' : getr R' 1 = Z_to_bv 64 WO_MS6_RA) by (rewrite L1; reflexivity).
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by (rewrite L9; reflexivity).
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 2776)) by (rewrite L10, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L18' : getr R' 18 = Z_to_bv 64 (ff + 3456)) by (rewrite L18, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L19' : getr R' 19 = Z_to_bv 64 (sh ff)) by (rewrite L19, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L20' : getr R' 20 = Z_to_bv 64 ff) by (rewrite L20; exact Q).
    assert (L21' : getr R' 21 = Z_to_bv 64 (ff + 2800)) by (rewrite L21, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 2752)) by (rewrite L27, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (MU1 : munch [(sh ff + 344, sh ff + 374); (ff + 2752, ff + 2776)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; unfold SHBASE; lia|]).
      apply Forall_nil. }
    assert (CT1 : rw_cells asegs M1 (ff + 2752) [C8 (Z_to_bv 64 words); C8 (Z_to_bv 64 nw); C8 (Z_to_bv 64 0)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 FSH S1L S1H SPH WT' Q Bwn.
      apply rw_cells_cons8_c; [lgc Hlf 2%nat ltac:(cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia);
                               first [apply WT'; cbn; lia | HLib.evs; reflexivity]|].
      apply rw_cells_cons8_c; [lgc Hlf 1%nat ltac:(cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia);
                               first [apply WT'; cbn; lia | HLib.evs; reflexivity]|].
      lgc Hlf 0%nat ltac:(cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia);
        first [apply WT'; cbn; lia | HLib.evs; reflexivity]. }
    assert (US1 : u8arr asegs M1 (sh ff) (map (Z_to_bv 8) WO_SH4T)).
    { subst M1. lazymatch type of ESb with bv_unsigned ?t = _ => replace (sh ff) with (bv_unsigned t + SHBASE) by (rewrite ESb; unfold SHBASE; lia) end.
      lazymatch type of Hlf with log_flat _ ?lg =>
        let l := eval vm_compute in (others (EMd M_MUL (ELit 8) (EVar 32)) lg) in
        assert (HO : others (EMd M_MUL (ELit 8) (EVar 32)) lg = l) by (vm_cast_no_check (@eq_refl _ l)) end.
      eapply u8arr_mem_denot with (base := WO_SH2C); [exact Hlf | | rewrite ESb; unfold SHBASE; lia | rewrite ESb; unfold SHBASE; cbn [length WO_SH2C app repeat]; lia
                              | rewrite ESb; replace (sh ff - 0x7fff8000 + SHBASE) with (sh ff) by (unfold SHBASE; lia); exact US
                              | vm_cast_no_check (@eq_refl _ (Some WO_SH4T))].
      intros i Hi. cbn [length WO_SH2C app repeat Z.of_nat Pos.of_succ_nat Pos.succ] in Hi.
      apply (lmiss_of_others _ _ _ _ 476); [| lia]. rewrite HO.
      clear - ES' EF' SHB FSH SHL F64 FLO FS1 S1L S1H SPH.
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?EF', ?ES', ?u64_of_Z by lia; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L9', L10', L11, L12, L18', L19', L20', L21', L24, L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. split; [exact CT1 | exact US1].
  Qed.

End WoR4.

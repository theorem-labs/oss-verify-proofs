(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib U0MemcpyBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import PropExec U0_code_1c000_1d000 U0_code_1d000_1d8c4.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

Module U0MemcpyAL.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StepTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.RefMemcpyLib OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.U0MemcpyBase.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.LiaFast.

Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AL.
Context {RCa1 : RunCtx}.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.


  Lemma b1_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    (0 <= k)%Z -> (k + 1 = n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d380 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    eexists. split.
    - mlbu F_1d2e0 D_1d2e0 k.
      msb F_1d2e4 D_1d2e4 k ltac:(apply sb_val_plain).
      replace (k + 1)%Z with n by lia.
      stepret F_1d2e8 D_1d2e8 ret ltac:(exact H1).
      apply mst_refl.
    - solve_keeps.
  Qed.


  Lemma t2_run : forall regs (ret : word) k m,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z ->
    (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z -> (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z ->
    (0 <= k)%Z -> (n - k = Z.land m 2 + Z.land m 1)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d348 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    -
      eexists. split.
      + stepn F_1d2a8 D_1d2a8.
        stepb_ft F_1d2ac D_1d2ac ltac:(cond).
        stepn F_1d2b0 D_1d2b0.
        stepb_ft F_1d2b4 D_1d2b4 ltac:(cond).
        stepret F_1d2b8 D_1d2b8 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d380 : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + eexists. split.
        * stepn F_1d2a8 D_1d2a8.
          stepb_ft F_1d2ac D_1d2ac ltac:(cond).
          stepn F_1d2b0 D_1d2b0.
          stepb_tk F_1d2b4 D_1d2b4 ltac:(cond).
          apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    -
      eexists. split.
      + stepn F_1d2a8 D_1d2a8.
        stepb_tk F_1d2ac D_1d2ac ltac:(cond).
        mlbu F_1d2bc D_1d2bc k.
        mlbu F_1d2c0 D_1d2c0 (k + 1)%Z.
        stepn F_1d2c4 D_1d2c4.
        stepn F_1d2c8 D_1d2c8.
        msb F_1d2cc D_1d2cc k ltac:(apply sb_val_plain).
        msb F_1d2d0 D_1d2d0 (k + 1)%Z ltac:(apply sb_val_plain).
        stepn F_1d2d4 D_1d2d4.
        stepn F_1d2d8 D_1d2d8.
        stepb_tk F_1d2dc D_1d2dc ltac:(cond).
        stepret F_1d2b8 D_1d2b8 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d380 : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + eexists. split.
        * stepn F_1d2a8 D_1d2a8.
          stepb_tk F_1d2ac D_1d2ac ltac:(cond).
          mlbu F_1d2bc D_1d2bc k.
          mlbu F_1d2c0 D_1d2c0 (k + 1)%Z.
          stepn F_1d2c4 D_1d2c4.
          stepn F_1d2c8 D_1d2c8.
          msb F_1d2cc D_1d2cc k ltac:(apply sb_val_plain).
          msb F_1d2d0 D_1d2d0 (k + 1)%Z ltac:(apply sb_val_plain).
          stepn F_1d2d4 D_1d2d4.
          stepn F_1d2d8 D_1d2d8.
          stepb_ft F_1d2dc D_1d2dc ltac:(cond).
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.


  Lemma al4_run : forall regs (ret : word) k m,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d104 : word) (MK k) rom)
                   (mkst regs' (0x1d348 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - eexists. split.
      + stepn F_1d064 D_1d064.
        stepb_tk F_1d068 D_1d068 ltac:(cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_1d064 D_1d064.
        stepb_ft F_1d068 D_1d068 ltac:(cond).
        mlw F_1d06c D_1d06c k.
        stepn F_1d070 D_1d070.
        msw F_1d074 D_1d074 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_1d078 D_1d078.
        stepn F_1d07c D_1d07c.
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  Lemma al8_run : forall regs (ret : word) k m e8,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d0e4 : word) (MK k) rom)
                   (mkst regs' (0x1d104 : word) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - eexists. split.
      + stepn F_1d044 D_1d044.
        stepb_tk F_1d048 D_1d048 ltac:(cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_1d044 D_1d044.
        stepb_ft F_1d048 D_1d048 ltac:(cond).
        mlw F_1d04c D_1d04c k.
        mlw F_1d050 D_1d050 (k + 4)%Z.
        msw F_1d054 D_1d054 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_1d058 D_1d058 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_1d05c D_1d05c.
        stepn F_1d060 D_1d060.
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  Lemma al_loop : forall (q : nat) regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 15 ->
    (0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d0b4 : word) (MK k) rom)
                   (mkst regs' (0x1d0e4 : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    -
      eexists. split.
      + mlw F_1d014 D_1d014 k.
        mlw F_1d018 D_1d018 (k + 4)%Z.
        mlw F_1d01c D_1d01c (k + 8)%Z.
        mlw F_1d020 D_1d020 (k + 12)%Z.
        stepn F_1d024 D_1d024.
        stepn F_1d028 D_1d028.
        msw F_1d02c D_1d02c k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_1d030 D_1d030 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_1d034 D_1d034 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_1d038 D_1d038 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_1d03c D_1d03c.
        stepb_ft F_1d040 D_1d040 ltac:(unfold v_addi; cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d0b4 : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * mlw F_1d014 D_1d014 k.
          mlw F_1d018 D_1d018 (k + 4)%Z.
          mlw F_1d01c D_1d01c (k + 8)%Z.
          mlw F_1d020 D_1d020 (k + 12)%Z.
          stepn F_1d024 D_1d024.
          stepn F_1d028 D_1d028.
          msw F_1d02c D_1d02c k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_1d030 D_1d030 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_1d034 D_1d034 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_1d038 D_1d038 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          stepn F_1d03c D_1d03c.
          stepb_tk F_1d040 D_1d040 ltac:(unfold v_addi; cond).
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
          -- unfold v_addi. unorm. f_equal. lia.
          -- solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. split.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
          decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  Lemma al16_run : forall regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d0a8 : word) (MK k) rom)
                   (mkst regs' (0x1d0e4 : word) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    -
      eexists. split.
      + stepn F_1d008 D_1d008.
        stepb_tk F_1d00c D_1d00c ltac:(cond).
        replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
        apply mst_refl.
      + rewrite (Z.mod_small (n - k) 16) by lia. replace (n - (n - k))%Z with k by lia.
        repeat split; gres; rwH; try reflexivity. solve_keeps.
    - set (q := Z.to_nat ((n - k) / 16 - 1)).
      assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
      assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d0b4 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * stepn F_1d008 D_1d008.
          stepb_ft F_1d00c D_1d00c ltac:(cond).
          stepn F_1d010 D_1d010.
          apply mst_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
        exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.


End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End U0MemcpyAL.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StepTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.RefMemcpyLib OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.U0MemcpyBase U0MemcpyAL.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.LiaFast.

Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MIS.
Context {RCa1 : RunCtx}.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac sbp := apply sb_val_plain.

  Lemma b4_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d31c : word) (MK k) rom) (mkst regs' (0x1d348 : word) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
    - mlbu F_1d27c D_1d27c k. mlbu F_1d280 D_1d280 (k+1)%Z. mlbu F_1d284 D_1d284 (k+2)%Z. mlbu F_1d288 D_1d288 (k+3)%Z.
      stepn F_1d28c D_1d28c.
      stepn F_1d290 D_1d290.
      msb F_1d294 D_1d294 k ltac:(sbp). msb F_1d298 D_1d298 (k+1)%Z ltac:(sbp).
      msb F_1d29c D_1d29c (k+2)%Z ltac:(sbp). msb F_1d2a0 D_1d2a0 (k+3)%Z ltac:(sbp).
      stepn F_1d2a4 D_1d2a4.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d2c8 : word) (MK k) rom) (mkst regs' (0x1d314 : word) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
    - mlbu F_1d228 D_1d228 k. mlbu F_1d22c D_1d22c (k+1)%Z. mlbu F_1d230 D_1d230 (k+2)%Z. mlbu F_1d234 D_1d234 (k+3)%Z.
      mlbu F_1d238 D_1d238 (k+4)%Z. mlbu F_1d23c D_1d23c (k+5)%Z. mlbu F_1d240 D_1d240 (k+6)%Z. mlbu F_1d244 D_1d244 (k+7)%Z.
      stepn F_1d248 D_1d248.
      msb F_1d24c D_1d24c k ltac:(sbp). msb F_1d250 D_1d250 (k+1)%Z ltac:(sbp).
      msb F_1d254 D_1d254 (k+2)%Z ltac:(sbp). msb F_1d258 D_1d258 (k+3)%Z ltac:(sbp).
      stepn F_1d25c D_1d25c.
      msb F_1d260 D_1d260 (k+4)%Z ltac:(sbp). msb F_1d264 D_1d264 (k+5)%Z ltac:(sbp).
      msb F_1d268 D_1d268 (k+6)%Z ltac:(sbp). msb F_1d26c D_1d26c (k+7)%Z ltac:(sbp).
      stepn F_1d270 D_1d270.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d234 : word) (MK k) rom) (mkst regs' (0x1d2c0 : word) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
    - mlbu F_1d194 D_1d194 k. mlbu F_1d198 D_1d198 (k+1)%Z. mlbu F_1d19c D_1d19c (k+2)%Z. mlbu F_1d1a0 D_1d1a0 (k+3)%Z.
      mlbu F_1d1a4 D_1d1a4 (k+4)%Z. mlbu F_1d1a8 D_1d1a8 (k+5)%Z. mlbu F_1d1ac D_1d1ac (k+6)%Z. mlbu F_1d1b0 D_1d1b0 (k+7)%Z.
      msb F_1d1b4 D_1d1b4 k ltac:(sbp). msb F_1d1b8 D_1d1b8 (k+1)%Z ltac:(sbp).
      msb F_1d1bc D_1d1bc (k+2)%Z ltac:(sbp). msb F_1d1c0 D_1d1c0 (k+3)%Z ltac:(sbp).
      mlbu F_1d1c4 D_1d1c4 (k+8)%Z. mlbu F_1d1c8 D_1d1c8 (k+9)%Z. mlbu F_1d1cc D_1d1cc (k+10)%Z. mlbu F_1d1d0 D_1d1d0 (k+11)%Z.
      msb F_1d1d4 D_1d1d4 (k+4)%Z ltac:(sbp). msb F_1d1d8 D_1d1d8 (k+5)%Z ltac:(sbp).
      msb F_1d1dc D_1d1dc (k+6)%Z ltac:(sbp). msb F_1d1e0 D_1d1e0 (k+7)%Z ltac:(sbp).
      mlbu F_1d1e4 D_1d1e4 (k+12)%Z. mlbu F_1d1e8 D_1d1e8 (k+13)%Z. mlbu F_1d1ec D_1d1ec (k+14)%Z. mlbu F_1d1f0 D_1d1f0 (k+15)%Z.
      stepn F_1d1f4 D_1d1f4.
      msb F_1d1f8 D_1d1f8 (k+8)%Z ltac:(sbp). msb F_1d1fc D_1d1fc (k+9)%Z ltac:(sbp).
      msb F_1d200 D_1d200 (k+10)%Z ltac:(sbp). msb F_1d204 D_1d204 (k+11)%Z ltac:(sbp).
      stepn F_1d208 D_1d208.
      msb F_1d20c D_1d20c (k+12)%Z ltac:(sbp). msb F_1d210 D_1d210 (k+13)%Z ltac:(sbp).
      msb F_1d214 D_1d214 (k+14)%Z ltac:(sbp). msb F_1d218 D_1d218 (k+15)%Z ltac:(sbp).
      stepn F_1d21c D_1d21c.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1cff0 : word) (MK k) rom) (mkst regs' (0x1d348 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_1cf50 D_1cf50.
        stepb_ft F_1cf54 D_1cf54 ltac:(cond).
        stepn F_1cf58 D_1cf58.
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d31c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_1cf50 D_1cf50.
          stepb_tk F_1cf54 D_1cf54 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Lemma b8_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d314 : word) (MK k) rom) (mkst regs' (0x1d348 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_1d274 D_1d274.
        stepb_tk F_1d278 D_1d278 ltac:(cond).
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d31c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_1d274 D_1d274.
          stepb_ft F_1d278 D_1d278 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Lemma t8_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1cfe8 : word) (MK k) rom)
                   (mkst regs' (0x1d348 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1cff0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_1cf48 D_1cf48.
          stepb_ft F_1cf4c D_1cf4c ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d2c8 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_1cf48 D_1cf48.
          stepb_tk F_1cf4c D_1cf4c ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d314 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
          split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Lemma b16_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d2c0 : word) (MK k) rom)
                   (mkst regs' (0x1d348 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1cff0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_1d220 D_1d220.
          stepb_tk F_1d224 D_1d224 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d2c8 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_1d220 D_1d220.
          stepb_ft F_1d224 D_1d224 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d314 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Lemma t16_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 32)%Z -> (0 <= k)%Z ->
    (k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1cfe0 : word) (MK k) rom)
                   (mkst regs' (0x1d348 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
    destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1cfe8 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_1cf40 D_1cf40.
          stepb_ft F_1cf44 D_1cf44 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d234 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_1cf40 D_1cf40.
          stepb_tk F_1cf44 D_1cf44 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1d2c0 : word) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

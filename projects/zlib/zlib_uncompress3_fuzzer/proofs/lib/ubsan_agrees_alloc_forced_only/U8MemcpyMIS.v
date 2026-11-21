(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress3_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib U8MemcpyBase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec U8Memcpy_code.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

Module U8MemcpyAL.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8MemcpyBase.

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
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x218f8 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    eexists. split.
    - mlbu F_217ac D_217ac k.
      msb F_217b0 D_217b0 k ltac:(apply sb_val_plain).
      replace (k + 1)%Z with n by lia.
      stepret F_217b4 D_217b4 ret ltac:(exact H1).
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
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x218c0 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    -
      eexists. split.
      + stepn F_21774 D_21774.
        stepb_ft F_21778 D_21778 ltac:(cond).
        stepn F_2177c D_2177c.
        stepb_ft F_21780 D_21780 ltac:(cond).
        stepret F_21784 D_21784 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x218f8 : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + eexists. split.
        * stepn F_21774 D_21774.
          stepb_ft F_21778 D_21778 ltac:(cond).
          stepn F_2177c D_2177c.
          stepb_tk F_21780 D_21780 ltac:(cond).
          apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    -
      eexists. split.
      + stepn F_21774 D_21774.
        stepb_tk F_21778 D_21778 ltac:(cond).
        mlbu F_21788 D_21788 k.
        mlbu F_2178c D_2178c (k + 1)%Z.
        stepn F_21790 D_21790.
        stepn F_21794 D_21794.
        msb F_21798 D_21798 k ltac:(apply sb_val_plain).
        msb F_2179c D_2179c (k + 1)%Z ltac:(apply sb_val_plain).
        stepn F_217a0 D_217a0.
        stepn F_217a4 D_217a4.
        stepb_tk F_217a8 D_217a8 ltac:(cond).
        stepret F_21784 D_21784 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x218f8 : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + eexists. split.
        * stepn F_21774 D_21774.
          stepb_tk F_21778 D_21778 ltac:(cond).
          mlbu F_21788 D_21788 k.
          mlbu F_2178c D_2178c (k + 1)%Z.
          stepn F_21790 D_21790.
          stepn F_21794 D_21794.
          msb F_21798 D_21798 k ltac:(apply sb_val_plain).
          msb F_2179c D_2179c (k + 1)%Z ltac:(apply sb_val_plain).
          stepn F_217a0 D_217a0.
          stepn F_217a4 D_217a4.
          stepb_ft F_217a8 D_217a8 ltac:(cond).
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
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x2167c : word) (MK k) rom)
                   (mkst regs' (0x218c0 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - eexists. split.
      + stepn F_21530 D_21530.
        stepb_tk F_21534 D_21534 ltac:(cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_21530 D_21530.
        stepb_ft F_21534 D_21534 ltac:(cond).
        mlw F_21538 D_21538 k.
        stepn F_2153c D_2153c.
        msw F_21540 D_21540 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_21544 D_21544.
        stepn F_21548 D_21548.
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  Lemma al8_run : forall regs (ret : word) k m e8,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x2165c : word) (MK k) rom)
                   (mkst regs' (0x2167c : word) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - eexists. split.
      + stepn F_21510 D_21510.
        stepb_tk F_21514 D_21514 ltac:(cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_21510 D_21510.
        stepb_ft F_21514 D_21514 ltac:(cond).
        mlw F_21518 D_21518 k.
        mlw F_2151c D_2151c (k + 4)%Z.
        msw F_21520 D_21520 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_21524 D_21524 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_21528 D_21528.
        stepn F_2152c D_2152c.
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  Lemma al_loop : forall (q : nat) regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 15 ->
    (0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x2162c : word) (MK k) rom)
                   (mkst regs' (0x2165c : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    -
      eexists. split.
      + mlw F_214e0 D_214e0 k.
        mlw F_214e4 D_214e4 (k + 4)%Z.
        mlw F_214e8 D_214e8 (k + 8)%Z.
        mlw F_214ec D_214ec (k + 12)%Z.
        stepn F_214f0 D_214f0.
        stepn F_214f4 D_214f4.
        msw F_214f8 D_214f8 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_214fc D_214fc (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_21500 D_21500 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_21504 D_21504 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_21508 D_21508.
        stepb_ft F_2150c D_2150c ltac:(unfold v_addi; cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x2162c : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * mlw F_214e0 D_214e0 k.
          mlw F_214e4 D_214e4 (k + 4)%Z.
          mlw F_214e8 D_214e8 (k + 8)%Z.
          mlw F_214ec D_214ec (k + 12)%Z.
          stepn F_214f0 D_214f0.
          stepn F_214f4 D_214f4.
          msw F_214f8 D_214f8 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_214fc D_214fc (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_21500 D_21500 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_21504 D_21504 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          stepn F_21508 D_21508.
          stepb_tk F_2150c D_2150c ltac:(unfold v_addi; cond).
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
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21620 : word) (MK k) rom)
                   (mkst regs' (0x2165c : word) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    -
      eexists. split.
      + stepn F_214d4 D_214d4.
        stepb_tk F_214d8 D_214d8 ltac:(cond).
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
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x2162c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * stepn F_214d4 D_214d4.
          stepb_ft F_214d8 D_214d8 ltac:(cond).
          stepn F_214dc D_214dc.
          apply mst_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
        exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.


End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End U8MemcpyAL.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8MemcpyBase U8MemcpyAL.

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
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21894 : word) (MK k) rom) (mkst regs' (0x218c0 : word) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
    - mlbu F_21748 D_21748 k. mlbu F_2174c D_2174c (k+1)%Z. mlbu F_21750 D_21750 (k+2)%Z. mlbu F_21754 D_21754 (k+3)%Z.
      stepn F_21758 D_21758.
      stepn F_2175c D_2175c.
      msb F_21760 D_21760 k ltac:(sbp). msb F_21764 D_21764 (k+1)%Z ltac:(sbp).
      msb F_21768 D_21768 (k+2)%Z ltac:(sbp). msb F_2176c D_2176c (k+3)%Z ltac:(sbp).
      stepn F_21770 D_21770.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21840 : word) (MK k) rom) (mkst regs' (0x2188c : word) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
    - mlbu F_216f4 D_216f4 k. mlbu F_216f8 D_216f8 (k+1)%Z. mlbu F_216fc D_216fc (k+2)%Z. mlbu F_21700 D_21700 (k+3)%Z.
      mlbu F_21704 D_21704 (k+4)%Z. mlbu F_21708 D_21708 (k+5)%Z. mlbu F_2170c D_2170c (k+6)%Z. mlbu F_21710 D_21710 (k+7)%Z.
      stepn F_21714 D_21714.
      msb F_21718 D_21718 k ltac:(sbp). msb F_2171c D_2171c (k+1)%Z ltac:(sbp).
      msb F_21720 D_21720 (k+2)%Z ltac:(sbp). msb F_21724 D_21724 (k+3)%Z ltac:(sbp).
      stepn F_21728 D_21728.
      msb F_2172c D_2172c (k+4)%Z ltac:(sbp). msb F_21730 D_21730 (k+5)%Z ltac:(sbp).
      msb F_21734 D_21734 (k+6)%Z ltac:(sbp). msb F_21738 D_21738 (k+7)%Z ltac:(sbp).
      stepn F_2173c D_2173c.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x217ac : word) (MK k) rom) (mkst regs' (0x21838 : word) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
    - mlbu F_21660 D_21660 k. mlbu F_21664 D_21664 (k+1)%Z. mlbu F_21668 D_21668 (k+2)%Z. mlbu F_2166c D_2166c (k+3)%Z.
      mlbu F_21670 D_21670 (k+4)%Z. mlbu F_21674 D_21674 (k+5)%Z. mlbu F_21678 D_21678 (k+6)%Z. mlbu F_2167c D_2167c (k+7)%Z.
      msb F_21680 D_21680 k ltac:(sbp). msb F_21684 D_21684 (k+1)%Z ltac:(sbp).
      msb F_21688 D_21688 (k+2)%Z ltac:(sbp). msb F_2168c D_2168c (k+3)%Z ltac:(sbp).
      mlbu F_21690 D_21690 (k+8)%Z. mlbu F_21694 D_21694 (k+9)%Z. mlbu F_21698 D_21698 (k+10)%Z. mlbu F_2169c D_2169c (k+11)%Z.
      msb F_216a0 D_216a0 (k+4)%Z ltac:(sbp). msb F_216a4 D_216a4 (k+5)%Z ltac:(sbp).
      msb F_216a8 D_216a8 (k+6)%Z ltac:(sbp). msb F_216ac D_216ac (k+7)%Z ltac:(sbp).
      mlbu F_216b0 D_216b0 (k+12)%Z. mlbu F_216b4 D_216b4 (k+13)%Z. mlbu F_216b8 D_216b8 (k+14)%Z. mlbu F_216bc D_216bc (k+15)%Z.
      stepn F_216c0 D_216c0.
      msb F_216c4 D_216c4 (k+8)%Z ltac:(sbp). msb F_216c8 D_216c8 (k+9)%Z ltac:(sbp).
      msb F_216cc D_216cc (k+10)%Z ltac:(sbp). msb F_216d0 D_216d0 (k+11)%Z ltac:(sbp).
      stepn F_216d4 D_216d4.
      msb F_216d8 D_216d8 (k+12)%Z ltac:(sbp). msb F_216dc D_216dc (k+13)%Z ltac:(sbp).
      msb F_216e0 D_216e0 (k+14)%Z ltac:(sbp). msb F_216e4 D_216e4 (k+15)%Z ltac:(sbp).
      stepn F_216e8 D_216e8.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21568 : word) (MK k) rom) (mkst regs' (0x218c0 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_2141c D_2141c.
        stepb_ft F_21420 D_21420 ltac:(cond).
        stepn F_21424 D_21424.
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x21894 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_2141c D_2141c.
          stepb_tk F_21420 D_21420 ltac:(cond).
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
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x2188c : word) (MK k) rom) (mkst regs' (0x218c0 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_21740 D_21740.
        stepb_tk F_21744 D_21744 ltac:(cond).
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x21894 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_21740 D_21740.
          stepb_ft F_21744 D_21744 ltac:(cond).
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
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21560 : word) (MK k) rom)
                   (mkst regs' (0x218c0 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x21568 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_21414 D_21414.
          stepb_ft F_21418 D_21418 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x21840 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_21414 D_21414.
          stepb_tk F_21418 D_21418 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x2188c : word) (MK (k + 8)) rom)
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
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21838 : word) (MK k) rom)
                   (mkst regs' (0x218c0 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x21568 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_216ec D_216ec.
          stepb_tk F_216f0 D_216f0 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x21840 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_216ec D_216ec.
          stepb_ft F_216f0 D_216f0 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x2188c : word) (MK (k + 8)) rom)
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
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21558 : word) (MK k) rom)
                   (mkst regs' (0x218c0 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
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
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x21560 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_2140c D_2140c.
          stepb_ft F_21410 D_21410 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    -
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x217ac : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_2140c D_2140c.
          stepb_tk F_21410 D_21410 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x21838 : word) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

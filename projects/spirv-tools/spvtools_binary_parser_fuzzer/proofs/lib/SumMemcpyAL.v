(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SumLib Sum_code.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim
  RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SumMemcpyBase.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AL.
Context {fx : FPState}.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemcpy_words.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH segs mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ _ HOK.

  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.

  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.

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
      msteps segs (mkst regs (at_ base 1016) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    eexists. split.
    - mlbu (MF_3f8 _ _ HCODE) D_118eb8 k.
      msb (MF_3fc _ _ HCODE) D_118ebc k ltac:(apply sb_val_plain).
      replace (k + 1)%Z with n by lia.
      aret (MF_400 _ _ HCODE) D_118ec0 ret.
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
      msteps segs (mkst regs (at_ base 960) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    -
      eexists. split.
      + an (MF_3c0 _ _ HCODE) D_118e80.
        ab_ft (MF_3c4 _ _ HCODE) D_118e84 ltac:(cond).
        an (MF_3c8 _ _ HCODE) D_118e88.
        ab_ft (MF_3cc _ _ HCODE) D_118e8c ltac:(cond).
        aret (MF_3d0 _ _ HCODE) D_118e90 ret.
        mk_eq. apply mst_refl.
      + solve_keeps.
    -
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 1016) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + eexists. split.
        * an (MF_3c0 _ _ HCODE) D_118e80.
          ab_ft (MF_3c4 _ _ HCODE) D_118e84 ltac:(cond).
          an (MF_3c8 _ _ HCODE) D_118e88.
          ab_tk (MF_3cc _ _ HCODE) D_118e8c ltac:(cond).
          apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    -
      eexists. split.
      + an (MF_3c0 _ _ HCODE) D_118e80.
        ab_tk (MF_3c4 _ _ HCODE) D_118e84 ltac:(cond).
        mlbu (MF_3d4 _ _ HCODE) D_118e94 k.
        mlbu (MF_3d8 _ _ HCODE) D_118e98 (k + 1)%Z.
        an (MF_3dc _ _ HCODE) D_118e9c.
        an (MF_3e0 _ _ HCODE) D_118ea0.
        msb (MF_3e4 _ _ HCODE) D_118ea4 k ltac:(apply sb_val_plain).
        msb (MF_3e8 _ _ HCODE) D_118ea8 (k + 1)%Z ltac:(apply sb_val_plain).
        an (MF_3ec _ _ HCODE) D_118eac.
        an (MF_3f0 _ _ HCODE) D_118eb0.
        ab_tk (MF_3f4 _ _ HCODE) D_118eb4 ltac:(cond).
        aret (MF_3d0 _ _ HCODE) D_118e90 ret.
        mk_eq. apply mst_refl.
      + solve_keeps.
    -
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 1016) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + eexists. split.
        * an (MF_3c0 _ _ HCODE) D_118e80.
          ab_tk (MF_3c4 _ _ HCODE) D_118e84 ltac:(cond).
          mlbu (MF_3d4 _ _ HCODE) D_118e94 k.
          mlbu (MF_3d8 _ _ HCODE) D_118e98 (k + 1)%Z.
          an (MF_3dc _ _ HCODE) D_118e9c.
          an (MF_3e0 _ _ HCODE) D_118ea0.
          msb (MF_3e4 _ _ HCODE) D_118ea4 k ltac:(apply sb_val_plain).
          msb (MF_3e8 _ _ HCODE) D_118ea8 (k + 1)%Z ltac:(apply sb_val_plain).
          an (MF_3ec _ _ HCODE) D_118eac.
          an (MF_3f0 _ _ HCODE) D_118eb0.
          ab_ft (MF_3f4 _ _ HCODE) D_118eb4 ltac:(cond).
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
      msteps segs (mkst regs (at_ base 380) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - eexists. split.
      + an (MF_17c _ _ HCODE) D_118c3c.
        ab_tk (MF_180 _ _ HCODE) D_118c40 ltac:(cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + an (MF_17c _ _ HCODE) D_118c3c.
        ab_ft (MF_180 _ _ HCODE) D_118c40 ltac:(cond).
        mlw (MF_184 _ _ HCODE) D_118c44 k.
        an (MF_188 _ _ HCODE) D_118c48.
        msw (MF_18c _ _ HCODE) D_118c4c k ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
        an (MF_190 _ _ HCODE) D_118c50.
        an (MF_194 _ _ HCODE) D_118c54.
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  Lemma al8_run : forall regs (ret : word) k m e8,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 348) (MK k) rom)
                   (mkst regs' (at_ base 380) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - eexists. split.
      + an (MF_15c _ _ HCODE) D_118c1c.
        ab_tk (MF_160 _ _ HCODE) D_118c20 ltac:(cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + an (MF_15c _ _ HCODE) D_118c1c.
        ab_ft (MF_160 _ _ HCODE) D_118c20 ltac:(cond).
        mlw (MF_164 _ _ HCODE) D_118c24 k.
        mlw (MF_168 _ _ HCODE) D_118c28 (k + 4)%Z.
        msw (MF_16c _ _ HCODE) D_118c2c k ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
        msw (MF_170 _ _ HCODE) D_118c30 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
        an (MF_174 _ _ HCODE) D_118c34.
        an (MF_178 _ _ HCODE) D_118c38.
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  Lemma al_loop : forall (q : nat) regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 15 ->
    (0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 300) (MK k) rom)
                   (mkst regs' (at_ base 348) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    -
      eexists. split.
      + mlw (MF_12c _ _ HCODE) D_118bec k.
        mlw (MF_130 _ _ HCODE) D_118bf0 (k + 4)%Z.
        mlw (MF_134 _ _ HCODE) D_118bf4 (k + 8)%Z.
        mlw (MF_138 _ _ HCODE) D_118bf8 (k + 12)%Z.
        an (MF_13c _ _ HCODE) D_118bfc.
        an (MF_140 _ _ HCODE) D_118c00.
        msw (MF_144 _ _ HCODE) D_118c04 k ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
        msw (MF_148 _ _ HCODE) D_118c08 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
        msw (MF_14c _ _ HCODE) D_118c0c (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
        msw (MF_150 _ _ HCODE) D_118c10 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
        an (MF_154 _ _ HCODE) D_118c14.
        ab_ft (MF_158 _ _ HCODE) D_118c18 ltac:(unfold v_addi; cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 300) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * mlw (MF_12c _ _ HCODE) D_118bec k.
          mlw (MF_130 _ _ HCODE) D_118bf0 (k + 4)%Z.
          mlw (MF_134 _ _ HCODE) D_118bf4 (k + 8)%Z.
          mlw (MF_138 _ _ HCODE) D_118bf8 (k + 12)%Z.
          an (MF_13c _ _ HCODE) D_118bfc.
          an (MF_140 _ _ HCODE) D_118c00.
          msw (MF_144 _ _ HCODE) D_118c04 k ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
          msw (MF_148 _ _ HCODE) D_118c08 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
          msw (MF_14c _ _ HCODE) D_118c0c (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
          msw (MF_150 _ _ HCODE) D_118c10 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
          an (MF_154 _ _ HCODE) D_118c14.
          ab_tk (MF_158 _ _ HCODE) D_118c18 ltac:(unfold v_addi; cond).
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
      msteps segs (mkst regs (at_ base 288) (MK k) rom)
                   (mkst regs' (at_ base 348) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    -
      eexists. split.
      + an (MF_120 _ _ HCODE) D_118be0.
        ab_tk (MF_124 _ _ HCODE) D_118be4 ltac:(cond).
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
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 300) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * an (MF_120 _ _ HCODE) D_118be0.
          ab_ft (MF_124 _ _ HCODE) D_118be4 ltac:(cond).
          an (MF_128 _ _ HCODE) D_118be8.
          apply mst_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
        exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

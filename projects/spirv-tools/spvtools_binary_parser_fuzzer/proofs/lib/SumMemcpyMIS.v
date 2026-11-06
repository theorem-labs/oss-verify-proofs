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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SumMemcpyBase SumMemcpyAL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MIS.
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

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac sbp := apply sb_val_plain.

  Lemma b4_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 916) (MK k) rom) (mkst regs' (at_ base 960) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
    - mlbu (MF_394 _ _ HCODE) D_118e54 k. mlbu (MF_398 _ _ HCODE) D_118e58 (k+1)%Z. mlbu (MF_39c _ _ HCODE) D_118e5c (k+2)%Z. mlbu (MF_3a0 _ _ HCODE) D_118e60 (k+3)%Z.
      an (MF_3a4 _ _ HCODE) D_118e64.
      an (MF_3a8 _ _ HCODE) D_118e68.
      msb (MF_3ac _ _ HCODE) D_118e6c k ltac:(sbp). msb (MF_3b0 _ _ HCODE) D_118e70 (k+1)%Z ltac:(sbp).
      msb (MF_3b4 _ _ HCODE) D_118e74 (k+2)%Z ltac:(sbp). msb (MF_3b8 _ _ HCODE) D_118e78 (k+3)%Z ltac:(sbp).
      an (MF_3bc _ _ HCODE) D_118e7c.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 832) (MK k) rom) (mkst regs' (at_ base 908) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
    - mlbu (MF_340 _ _ HCODE) D_118e00 k. mlbu (MF_344 _ _ HCODE) D_118e04 (k+1)%Z. mlbu (MF_348 _ _ HCODE) D_118e08 (k+2)%Z. mlbu (MF_34c _ _ HCODE) D_118e0c (k+3)%Z.
      mlbu (MF_350 _ _ HCODE) D_118e10 (k+4)%Z. mlbu (MF_354 _ _ HCODE) D_118e14 (k+5)%Z. mlbu (MF_358 _ _ HCODE) D_118e18 (k+6)%Z. mlbu (MF_35c _ _ HCODE) D_118e1c (k+7)%Z.
      an (MF_360 _ _ HCODE) D_118e20.
      msb (MF_364 _ _ HCODE) D_118e24 k ltac:(sbp). msb (MF_368 _ _ HCODE) D_118e28 (k+1)%Z ltac:(sbp).
      msb (MF_36c _ _ HCODE) D_118e2c (k+2)%Z ltac:(sbp). msb (MF_370 _ _ HCODE) D_118e30 (k+3)%Z ltac:(sbp).
      an (MF_374 _ _ HCODE) D_118e34.
      msb (MF_378 _ _ HCODE) D_118e38 (k+4)%Z ltac:(sbp). msb (MF_37c _ _ HCODE) D_118e3c (k+5)%Z ltac:(sbp).
      msb (MF_380 _ _ HCODE) D_118e40 (k+6)%Z ltac:(sbp). msb (MF_384 _ _ HCODE) D_118e44 (k+7)%Z ltac:(sbp).
      an (MF_388 _ _ HCODE) D_118e48.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 684) (MK k) rom) (mkst regs' (at_ base 824) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
    - mlbu (MF_2ac _ _ HCODE) D_118d6c k. mlbu (MF_2b0 _ _ HCODE) D_118d70 (k+1)%Z. mlbu (MF_2b4 _ _ HCODE) D_118d74 (k+2)%Z. mlbu (MF_2b8 _ _ HCODE) D_118d78 (k+3)%Z.
      mlbu (MF_2bc _ _ HCODE) D_118d7c (k+4)%Z. mlbu (MF_2c0 _ _ HCODE) D_118d80 (k+5)%Z. mlbu (MF_2c4 _ _ HCODE) D_118d84 (k+6)%Z. mlbu (MF_2c8 _ _ HCODE) D_118d88 (k+7)%Z.
      msb (MF_2cc _ _ HCODE) D_118d8c k ltac:(sbp). msb (MF_2d0 _ _ HCODE) D_118d90 (k+1)%Z ltac:(sbp).
      msb (MF_2d4 _ _ HCODE) D_118d94 (k+2)%Z ltac:(sbp). msb (MF_2d8 _ _ HCODE) D_118d98 (k+3)%Z ltac:(sbp).
      mlbu (MF_2dc _ _ HCODE) D_118d9c (k+8)%Z. mlbu (MF_2e0 _ _ HCODE) D_118da0 (k+9)%Z. mlbu (MF_2e4 _ _ HCODE) D_118da4 (k+10)%Z. mlbu (MF_2e8 _ _ HCODE) D_118da8 (k+11)%Z.
      msb (MF_2ec _ _ HCODE) D_118dac (k+4)%Z ltac:(sbp). msb (MF_2f0 _ _ HCODE) D_118db0 (k+5)%Z ltac:(sbp).
      msb (MF_2f4 _ _ HCODE) D_118db4 (k+6)%Z ltac:(sbp). msb (MF_2f8 _ _ HCODE) D_118db8 (k+7)%Z ltac:(sbp).
      mlbu (MF_2fc _ _ HCODE) D_118dbc (k+12)%Z. mlbu (MF_300 _ _ HCODE) D_118dc0 (k+13)%Z. mlbu (MF_304 _ _ HCODE) D_118dc4 (k+14)%Z. mlbu (MF_308 _ _ HCODE) D_118dc8 (k+15)%Z.
      an (MF_30c _ _ HCODE) D_118dcc.
      msb (MF_310 _ _ HCODE) D_118dd0 (k+8)%Z ltac:(sbp). msb (MF_314 _ _ HCODE) D_118dd4 (k+9)%Z ltac:(sbp).
      msb (MF_318 _ _ HCODE) D_118dd8 (k+10)%Z ltac:(sbp). msb (MF_31c _ _ HCODE) D_118ddc (k+11)%Z ltac:(sbp).
      an (MF_320 _ _ HCODE) D_118de0.
      msb (MF_324 _ _ HCODE) D_118de4 (k+12)%Z ltac:(sbp). msb (MF_328 _ _ HCODE) D_118de8 (k+13)%Z ltac:(sbp).
      msb (MF_32c _ _ HCODE) D_118dec (k+14)%Z ltac:(sbp). msb (MF_330 _ _ HCODE) D_118df0 (k+15)%Z ltac:(sbp).
      an (MF_334 _ _ HCODE) D_118df4.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 104) (MK k) rom) (mkst regs' (at_ base 960) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + an (MF_068 _ _ HCODE) D_118b28.
        ab_ft (MF_06c _ _ HCODE) D_118b2c ltac:(cond).
        an (MF_070 _ _ HCODE) D_118b30.
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 916) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * an (MF_068 _ _ HCODE) D_118b28.
          ab_tk (MF_06c _ _ HCODE) D_118b2c ltac:(cond).
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
      msteps segs (mkst regs (at_ base 908) (MK k) rom) (mkst regs' (at_ base 960) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + an (MF_38c _ _ HCODE) D_118e4c.
        ab_tk (MF_390 _ _ HCODE) D_118e50 ltac:(cond).
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 916) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * an (MF_38c _ _ HCODE) D_118e4c.
          ab_ft (MF_390 _ _ HCODE) D_118e50 ltac:(cond).
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
      msteps segs (mkst regs (at_ base 96) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    -
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 104) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * an (MF_060 _ _ HCODE) D_118b20.
          ab_ft (MF_064 _ _ HCODE) D_118b24 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    -
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 832) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * an (MF_060 _ _ HCODE) D_118b20.
          ab_tk (MF_064 _ _ HCODE) D_118b24 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 908) (MK (k + 8)) rom)
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
      msteps segs (mkst regs (at_ base 824) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 104) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * an (MF_338 _ _ HCODE) D_118df8.
          ab_tk (MF_33c _ _ HCODE) D_118dfc ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 832) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * an (MF_338 _ _ HCODE) D_118df8.
          ab_ft (MF_33c _ _ HCODE) D_118dfc ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 908) (MK (k + 8)) rom)
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
      msteps segs (mkst regs (at_ base 88) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
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
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 96) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * an (MF_058 _ _ HCODE) D_118b18.
          ab_ft (MF_05c _ _ HCODE) D_118b1c ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    -
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 684) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * an (MF_058 _ _ HCODE) D_118b18.
          ab_tk (MF_05c _ _ HCODE) D_118b1c ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 824) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

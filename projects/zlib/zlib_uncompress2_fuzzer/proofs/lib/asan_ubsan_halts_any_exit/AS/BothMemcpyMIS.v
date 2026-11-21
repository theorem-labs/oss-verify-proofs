(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress2_fuzzer_both.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim
  RefMemcpyLib BothMemcpyBase BothMemcpyAL Both_code_memcpy.
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MIS.
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
      msteps BSEGS (mkst regs (0xc7c9c : word) (MK k) rom) (mkst regs' (0xc7cc8 : word) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
    - mlbu F_c767c D_c767c k. mlbu F_c7680 D_c7680 (k+1)%Z. mlbu F_c7684 D_c7684 (k+2)%Z. mlbu F_c7688 D_c7688 (k+3)%Z.
      stepn F_c768c D_c768c.
      stepn F_c7690 D_c7690.
      msb F_c7694 D_c7694 k ltac:(sbp). msb F_c7698 D_c7698 (k+1)%Z ltac:(sbp).
      msb F_c769c D_c769c (k+2)%Z ltac:(sbp). msb F_c76a0 D_c76a0 (k+3)%Z ltac:(sbp).
      stepn F_c76a4 D_c76a4.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xc7c48 : word) (MK k) rom) (mkst regs' (0xc7c94 : word) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
    - mlbu F_c7628 D_c7628 k. mlbu F_c762c D_c762c (k+1)%Z. mlbu F_c7630 D_c7630 (k+2)%Z. mlbu F_c7634 D_c7634 (k+3)%Z.
      mlbu F_c7638 D_c7638 (k+4)%Z. mlbu F_c763c D_c763c (k+5)%Z. mlbu F_c7640 D_c7640 (k+6)%Z. mlbu F_c7644 D_c7644 (k+7)%Z.
      stepn F_c7648 D_c7648.
      msb F_c764c D_c764c k ltac:(sbp). msb F_c7650 D_c7650 (k+1)%Z ltac:(sbp).
      msb F_c7654 D_c7654 (k+2)%Z ltac:(sbp). msb F_c7658 D_c7658 (k+3)%Z ltac:(sbp).
      stepn F_c765c D_c765c.
      msb F_c7660 D_c7660 (k+4)%Z ltac:(sbp). msb F_c7664 D_c7664 (k+5)%Z ltac:(sbp).
      msb F_c7668 D_c7668 (k+6)%Z ltac:(sbp). msb F_c766c D_c766c (k+7)%Z ltac:(sbp).
      stepn F_c7670 D_c7670.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xc7bb4 : word) (MK k) rom) (mkst regs' (0xc7c40 : word) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
    - mlbu F_c7594 D_c7594 k. mlbu F_c7598 D_c7598 (k+1)%Z. mlbu F_c759c D_c759c (k+2)%Z. mlbu F_c75a0 D_c75a0 (k+3)%Z.
      mlbu F_c75a4 D_c75a4 (k+4)%Z. mlbu F_c75a8 D_c75a8 (k+5)%Z. mlbu F_c75ac D_c75ac (k+6)%Z. mlbu F_c75b0 D_c75b0 (k+7)%Z.
      msb F_c75b4 D_c75b4 k ltac:(sbp). msb F_c75b8 D_c75b8 (k+1)%Z ltac:(sbp).
      msb F_c75bc D_c75bc (k+2)%Z ltac:(sbp). msb F_c75c0 D_c75c0 (k+3)%Z ltac:(sbp).
      mlbu F_c75c4 D_c75c4 (k+8)%Z. mlbu F_c75c8 D_c75c8 (k+9)%Z. mlbu F_c75cc D_c75cc (k+10)%Z. mlbu F_c75d0 D_c75d0 (k+11)%Z.
      msb F_c75d4 D_c75d4 (k+4)%Z ltac:(sbp). msb F_c75d8 D_c75d8 (k+5)%Z ltac:(sbp).
      msb F_c75dc D_c75dc (k+6)%Z ltac:(sbp). msb F_c75e0 D_c75e0 (k+7)%Z ltac:(sbp).
      mlbu F_c75e4 D_c75e4 (k+12)%Z. mlbu F_c75e8 D_c75e8 (k+13)%Z. mlbu F_c75ec D_c75ec (k+14)%Z. mlbu F_c75f0 D_c75f0 (k+15)%Z.
      stepn F_c75f4 D_c75f4.
      msb F_c75f8 D_c75f8 (k+8)%Z ltac:(sbp). msb F_c75fc D_c75fc (k+9)%Z ltac:(sbp).
      msb F_c7600 D_c7600 (k+10)%Z ltac:(sbp). msb F_c7604 D_c7604 (k+11)%Z ltac:(sbp).
      stepn F_c7608 D_c7608.
      msb F_c760c D_c760c (k+12)%Z ltac:(sbp). msb F_c7610 D_c7610 (k+13)%Z ltac:(sbp).
      msb F_c7614 D_c7614 (k+14)%Z ltac:(sbp). msb F_c7618 D_c7618 (k+15)%Z ltac:(sbp).
      stepn F_c761c D_c761c.
      mk_eq. apply mst_refl.
    - post.
  Qed.

  Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xc7970 : word) (MK k) rom) (mkst regs' (0xc7cc8 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_c7350 D_c7350.
        stepb_ft F_c7354 D_c7354 ltac:(cond).
        stepn F_c7358 D_c7358.
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xc7c9c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_c7350 D_c7350.
          stepb_tk F_c7354 D_c7354 ltac:(cond).
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
      msteps BSEGS (mkst regs (0xc7c94 : word) (MK k) rom) (mkst regs' (0xc7cc8 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_c7674 D_c7674.
        stepb_tk F_c7678 D_c7678 ltac:(cond).
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xc7c9c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_c7674 D_c7674.
          stepb_ft F_c7678 D_c7678 ltac:(cond).
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
      msteps BSEGS (mkst regs (0xc7968 : word) (MK k) rom)
                   (mkst regs' (0xc7cc8 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    -
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xc7970 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_c7348 D_c7348.
          stepb_ft F_c734c D_c734c ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    -
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xc7c48 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_c7348 D_c7348.
          stepb_tk F_c734c D_c734c ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans BSEGS _ (fun r => mkst r (0xc7c94 : word) (MK (k + 8)) rom)
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
      msteps BSEGS (mkst regs (0xc7c40 : word) (MK k) rom)
                   (mkst regs' (0xc7cc8 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xc7970 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_c7620 D_c7620.
          stepb_tk F_c7624 D_c7624 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xc7c48 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_c7620 D_c7620.
          stepb_ft F_c7624 D_c7624 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans BSEGS _ (fun r => mkst r (0xc7c94 : word) (MK (k + 8)) rom)
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
      msteps BSEGS (mkst regs (0xc7960 : word) (MK k) rom)
                   (mkst regs' (0xc7cc8 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
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
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xc7968 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_c7340 D_c7340.
          stepb_ft F_c7344 D_c7344 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    -
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xc7bb4 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_c7340 D_c7340.
          stepb_tk F_c7344 D_c7344 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans BSEGS _ (fun r => mkst r (0xc7c40 : word) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

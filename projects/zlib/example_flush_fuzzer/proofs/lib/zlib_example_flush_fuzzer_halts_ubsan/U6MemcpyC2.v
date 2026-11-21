(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.World Require Import Tgt_example_flush_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib U6MemcpyBase U6MemcpyMIS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.WalkTac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.MmapSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.RefMemcpyLib OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.U6MemcpyBase OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.U6MemcpyMIS.U6MemcpyAL OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.U6MemcpyMIS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import U6_code_2a000_2b000   .
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Section C2.
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
  Ltac m16 := eapply (merge_s16 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  Lemma c2_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2a898 : word) (MK k) rom) (mkst regs' (0x2a8c8 : word) (MK (k + 2)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 2)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 2)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 17 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
    - mlw F_2a72c D_2a72c k.
      stepn F_2a730 D_2a730.
      stepb_ft F_2a734 D_2a734 ltac:(cond).
      stepn F_2a738 D_2a738.
      stepb_ft F_2a73c D_2a73c ltac:(cond).
      stepn F_2a740 D_2a740.
      stepn F_2a744 D_2a744.
      msb F_2a748 D_2a748 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
      msb F_2a74c D_2a74c (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).
      stepn F_2a750 D_2a750.
      stepn F_2a754 D_2a754.
      stepn F_2a758 D_2a758.
      mk_eq. apply mst_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  Lemma c2_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 17 ->
    (ja = kk + 14)%Z -> (jw = kk - 2)%Z -> (2 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 2 <= n - kk < 16 * (Z.of_nat q + 1) + 18)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x2a8c8 : word) (MK kk) rom)
                   (mkst regs' (0x2a928 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 14)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - eexists. split.
      + stepn F_2a75c D_2a75c.
        mlw F_2a760 D_2a760 (kk + 2)%Z.
        mlw F_2a764 D_2a764 (kk + 6)%Z.
        mlw F_2a768 D_2a768 (kk + 10)%Z.
        mlw F_2a76c D_2a76c (kk + 14)%Z.
        stepn F_2a770 D_2a770. stepn F_2a774 D_2a774. stepn F_2a778 D_2a778.
        stepn F_2a77c D_2a77c. stepn F_2a780 D_2a780. stepn F_2a784 D_2a784.
        stepn F_2a788 D_2a788. stepn F_2a78c D_2a78c. stepn F_2a790 D_2a790.
        stepn F_2a794 D_2a794. stepn F_2a798 D_2a798.
        stepn F_2a79c D_2a79c.
        msw F_2a7a0 D_2a7a0 kk ltac:(m16).
        msw F_2a7a4 D_2a7a4 (kk + 4)%Z ltac:(m16).
        msw F_2a7a8 D_2a7a8 (kk + 8)%Z ltac:(m16).
        msw F_2a7ac D_2a7ac (kk + 12)%Z ltac:(m16).
        stepn F_2a7b0 D_2a7b0.
        stepn F_2a7b4 D_2a7b4.
        stepb_ft F_2a7b8 D_2a7b8 ltac:(unfold v_addi; cond).
        mk_eq. apply mst_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x2a8c8 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
                         /\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
      + eexists. split.
        * stepn F_2a75c D_2a75c.
          mlw F_2a760 D_2a760 (kk + 2)%Z.
          mlw F_2a764 D_2a764 (kk + 6)%Z.
          mlw F_2a768 D_2a768 (kk + 10)%Z.
          mlw F_2a76c D_2a76c (kk + 14)%Z.
          stepn F_2a770 D_2a770. stepn F_2a774 D_2a774. stepn F_2a778 D_2a778.
          stepn F_2a77c D_2a77c. stepn F_2a780 D_2a780. stepn F_2a784 D_2a784.
          stepn F_2a788 D_2a788. stepn F_2a78c D_2a78c. stepn F_2a790 D_2a790.
          stepn F_2a794 D_2a794. stepn F_2a798 D_2a798.
          stepn F_2a79c D_2a79c.
          msw F_2a7a0 D_2a7a0 kk ltac:(m16).
          msw F_2a7a4 D_2a7a4 (kk + 4)%Z ltac:(m16).
          msw F_2a7a8 D_2a7a8 (kk + 8)%Z ltac:(m16).
          msw F_2a7ac D_2a7ac (kk + 12)%Z ltac:(m16).
          stepn F_2a7b0 D_2a7b0.
          stepn F_2a7b4 D_2a7b4.
          stepb_tk F_2a7b8 D_2a7b8 ltac:(unfold v_addi; cond).
          mk_eq. apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Lemma c2_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 14) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps RSEGS (mkst regs (0x2a928 : word) (MK kk) rom)
                   (mkst regs' (0x2abe4 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    -
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2a884 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_2a7bc D_2a7bc.
          stepn F_2a7c0 D_2a7c0.
          stepb_tk F_2a7c4 D_2a7c4 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    -
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x2aad0 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_2a7bc D_2a7bc.
          stepn F_2a7c0 D_2a7c0.
          stepb_ft F_2a7c4 D_2a7c4 ltac:(cond).
          stepn F_2a7c8 D_2a7c8.
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x2ab5c : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  Lemma c2_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps RSEGS (mkst regs (0x2a898 : word) (MK k) rom)
                   (mkst regs' (0x2abe4 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C2.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

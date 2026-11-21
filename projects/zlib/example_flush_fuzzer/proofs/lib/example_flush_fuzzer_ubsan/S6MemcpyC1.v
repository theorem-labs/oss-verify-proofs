(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib S6MemcpyBase S6MemcpyMIS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.WalkTac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.MmapSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.RefMemcpyLib OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.S6MemcpyBase OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.S6MemcpyMIS.S6MemcpyAL OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.S6MemcpyMIS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import S6_code_27000_28000  .
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Section C1.
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
  Ltac m24 := eapply (merge_s24 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  Lemma c1_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x27874 : word) (MK k) rom) (mkst regs' (0x27a40 : word) (MK (k + 3)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 3)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
    - mlw F_2773c D_2773c k.
      stepn F_27740 D_27740.
      stepb_ft F_27744 D_27744 ltac:(cond).
      stepn F_27748 D_27748.
      stepb_tk F_2774c D_2774c ltac:(cond).
      stepn F_278e4 D_278e4.
      stepn F_278e8 D_278e8.
      stepn F_278ec D_278ec.
      msb F_278f0 D_278f0 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
      msb F_278f4 D_278f4 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).
      msb F_278f8 D_278f8 (k + 2)%Z ltac:(eapply (sb_val_srli16 _ _ _ _ _ HOK); lia).
      stepn F_278fc D_278fc.
      stepn F_27900 D_27900.
      stepn F_27904 D_27904.
      mk_eq. apply mst_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  Lemma c1_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 16 ->
    (ja = kk + 13)%Z -> (jw = kk - 3)%Z -> (3 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x27a40 : word) (MK kk) rom)
                   (mkst regs' (0x27aa0 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - eexists. split.
      + stepn F_27908 D_27908.
        mlw F_2790c D_2790c (kk + 1)%Z.
        mlw F_27910 D_27910 (kk + 5)%Z.
        mlw F_27914 D_27914 (kk + 9)%Z.
        mlw F_27918 D_27918 (kk + 13)%Z.
        stepn F_2791c D_2791c. stepn F_27920 D_27920. stepn F_27924 D_27924.
        stepn F_27928 D_27928. stepn F_2792c D_2792c. stepn F_27930 D_27930.
        stepn F_27934 D_27934. stepn F_27938 D_27938. stepn F_2793c D_2793c.
        stepn F_27940 D_27940. stepn F_27944 D_27944.
        stepn F_27948 D_27948.
        msw F_2794c D_2794c kk ltac:(m24).
        msw F_27950 D_27950 (kk + 4)%Z ltac:(m24).
        msw F_27954 D_27954 (kk + 8)%Z ltac:(m24).
        msw F_27958 D_27958 (kk + 12)%Z ltac:(m24).
        stepn F_2795c D_2795c.
        stepn F_27960 D_27960.
        stepb_ft F_27964 D_27964 ltac:(unfold v_addi; cond).
        mk_eq. apply mst_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x27a40 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 13) 4)
                         /\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
      + eexists. split.
        * stepn F_27908 D_27908.
          mlw F_2790c D_2790c (kk + 1)%Z.
          mlw F_27910 D_27910 (kk + 5)%Z.
          mlw F_27914 D_27914 (kk + 9)%Z.
          mlw F_27918 D_27918 (kk + 13)%Z.
          stepn F_2791c D_2791c. stepn F_27920 D_27920. stepn F_27924 D_27924.
          stepn F_27928 D_27928. stepn F_2792c D_2792c. stepn F_27930 D_27930.
          stepn F_27934 D_27934. stepn F_27938 D_27938. stepn F_2793c D_2793c.
          stepn F_27940 D_27940. stepn F_27944 D_27944.
          stepn F_27948 D_27948.
          msw F_2794c D_2794c kk ltac:(m24).
          msw F_27950 D_27950 (kk + 4)%Z ltac:(m24).
          msw F_27954 D_27954 (kk + 8)%Z ltac:(m24).
          msw F_27958 D_27958 (kk + 12)%Z ltac:(m24).
          stepn F_2795c D_2795c.
          stepn F_27960 D_27960.
          stepb_tk F_27964 D_27964 ltac:(unfold v_addi; cond).
          mk_eq. apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Lemma c1_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps RSEGS (mkst regs (0x27aa0 : word) (MK kk) rom)
                   (mkst regs' (0x27bc0 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x27860 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_27968 D_27968.
          stepn F_2796c D_2796c.
          stepb_tk F_27970 D_27970 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x27aac : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_27968 D_27968.
          stepn F_2796c D_2796c.
          stepb_ft F_27970 D_27970 ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x27b38 : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  Lemma c1_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps RSEGS (mkst regs (0x27874 : word) (MK k) rom)
                   (mkst regs' (0x27bc0 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C1.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

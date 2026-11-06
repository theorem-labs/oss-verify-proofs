(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim
  RefMemcpyLib BothMemcpyBase Both_code_memcpy.

Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AL.
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

  #[using="mem0 n bs HOK Hn0"] Lemma al_entry : forall regs (mem : word -> option byte),
    getr regs 10 = dst -> getr regs 11 = src ->
    (bv_unsigned src mod 4 = 0)%Z -> (bv_unsigned dst mod 4 = 0)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa2a7c : word) mem rom) (mkst regs' (0xa2b9c : word) mem rom)
      /\ getr regs' 13 = at_ dst 0 /\ getr regs' 11 = at_ src 0 /\ getr regs' 12 = getr regs 12
      /\ getr regs' 1 = getr regs 1 /\ keeps regs regs'.
  Proof.
    intros regs mem H10 H11 Hs4 Hd4.
    pose proof (u64_range src). pose proof (u64_range dst).
    eexists. split.
    - stepn F_a22e4 D_a22e4.
      stepb_tk F_a22e8 D_a22e8
        ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
      stepn F_a23f8 D_a23f8.
      stepn F_a23fc D_a23fc.
      stepb_ft F_a2400 D_a2400
        ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
      apply mst_refl.
    - repeat split; gres; rwH; rewrite ?at_0; try reflexivity. solve_keeps.
  Qed.

  #[using="HOK Hn0"] Lemma b1_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    (0 <= k)%Z -> (k + 1 = n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa2e74 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    eexists. split.
    - mlbu F_a26dc D_a26dc k.
      msb F_a26e0 D_a26e0 k ltac:(apply sb_val_plain).
      replace (k + 1)%Z with n by lia.
      stepret F_a26e4 D_a26e4 ret ltac:(exact H1).
      apply mst_refl.
    - solve_keeps.
  Qed.

  #[using="HOK Hn0"] Lemma t2_run : forall regs (ret : word) k m,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z ->
    (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z -> (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z ->
    (0 <= k)%Z -> (n - k = Z.land m 2 + Z.land m 1)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa2e3c : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    -
      eexists. split.
      + stepn F_a26a4 D_a26a4.
        stepb_ft F_a26a8 D_a26a8 ltac:(cond).
        stepn F_a26ac D_a26ac.
        stepb_ft F_a26b0 D_a26b0 ltac:(cond).
        stepret F_a26b4 D_a26b4 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    -
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa2e74 : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + eexists. split.
        * stepn F_a26a4 D_a26a4.
          stepb_ft F_a26a8 D_a26a8 ltac:(cond).
          stepn F_a26ac D_a26ac.
          stepb_tk F_a26b0 D_a26b0 ltac:(cond).
          apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    -
      eexists. split.
      + stepn F_a26a4 D_a26a4.
        stepb_tk F_a26a8 D_a26a8 ltac:(cond).
        mlbu F_a26b8 D_a26b8 k.
        mlbu F_a26bc D_a26bc (k + 1)%Z.
        stepn F_a26c0 D_a26c0.
        stepn F_a26c4 D_a26c4.
        msb F_a26c8 D_a26c8 k ltac:(apply sb_val_plain).
        msb F_a26cc D_a26cc (k + 1)%Z ltac:(apply sb_val_plain).
        stepn F_a26d0 D_a26d0.
        stepn F_a26d4 D_a26d4.
        stepb_tk F_a26d8 D_a26d8 ltac:(cond).
        stepret F_a26b4 D_a26b4 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    -
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa2e74 : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + eexists. split.
        * stepn F_a26a4 D_a26a4.
          stepb_tk F_a26a8 D_a26a8 ltac:(cond).
          mlbu F_a26b8 D_a26b8 k.
          mlbu F_a26bc D_a26bc (k + 1)%Z.
          stepn F_a26c0 D_a26c0.
          stepn F_a26c4 D_a26c4.
          msb F_a26c8 D_a26c8 k ltac:(apply sb_val_plain).
          msb F_a26cc D_a26cc (k + 1)%Z ltac:(apply sb_val_plain).
          stepn F_a26d0 D_a26d0.
          stepn F_a26d4 D_a26d4.
          stepb_ft F_a26d8 D_a26d8 ltac:(cond).
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  #[using="HOK Hn0"] Lemma al4_run : forall regs (ret : word) k m,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa2bf8 : word) (MK k) rom)
                   (mkst regs' (0xa2e3c : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - eexists. split.
      + stepn F_a2460 D_a2460.
        stepb_tk F_a2464 D_a2464 ltac:(cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_a2460 D_a2460.
        stepb_ft F_a2464 D_a2464 ltac:(cond).
        mlw F_a2468 D_a2468 k.
        stepn F_a246c D_a246c.
        msw F_a2470 D_a2470 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_a2474 D_a2474.
        stepn F_a2478 D_a2478.
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  #[using="HOK Hn0"] Lemma al8_run : forall regs (ret : word) k m e8,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa2bd8 : word) (MK k) rom)
                   (mkst regs' (0xa2bf8 : word) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - eexists. split.
      + stepn F_a2440 D_a2440.
        stepb_tk F_a2444 D_a2444 ltac:(cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_a2440 D_a2440.
        stepb_ft F_a2444 D_a2444 ltac:(cond).
        mlw F_a2448 D_a2448 k.
        mlw F_a244c D_a244c (k + 4)%Z.
        msw F_a2450 D_a2450 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_a2454 D_a2454 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_a2458 D_a2458.
        stepn F_a245c D_a245c.
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  #[using="HOK Hn0"] Lemma al_loop : forall (q : nat) regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 15 ->
    (0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa2ba8 : word) (MK k) rom)
                   (mkst regs' (0xa2bd8 : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    -
      eexists. split.
      + mlw F_a2410 D_a2410 k.
        mlw F_a2414 D_a2414 (k + 4)%Z.
        mlw F_a2418 D_a2418 (k + 8)%Z.
        mlw F_a241c D_a241c (k + 12)%Z.
        stepn F_a2420 D_a2420.
        stepn F_a2424 D_a2424.
        msw F_a2428 D_a2428 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_a242c D_a242c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_a2430 D_a2430 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_a2434 D_a2434 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_a2438 D_a2438.
        stepb_ft F_a243c D_a243c ltac:(unfold v_addi; cond).
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa2ba8 : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * mlw F_a2410 D_a2410 k.
          mlw F_a2414 D_a2414 (k + 4)%Z.
          mlw F_a2418 D_a2418 (k + 8)%Z.
          mlw F_a241c D_a241c (k + 12)%Z.
          stepn F_a2420 D_a2420.
          stepn F_a2424 D_a2424.
          msw F_a2428 D_a2428 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_a242c D_a242c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_a2430 D_a2430 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_a2434 D_a2434 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          stepn F_a2438 D_a2438.
          stepb_tk F_a243c D_a243c ltac:(unfold v_addi; cond).
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

  #[using="HOK Hn0"] Lemma al16_run : forall regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa2b9c : word) (MK k) rom)
                   (mkst regs' (0xa2bd8 : word) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    -
      eexists. split.
      + stepn F_a2404 D_a2404.
        stepb_tk F_a2408 D_a2408 ltac:(cond).
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
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa2ba8 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * stepn F_a2404 D_a2404.
          stepb_ft F_a2408 D_a2408 ltac:(cond).
          stepn F_a240c D_a240c.
          apply mst_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
        exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  #[using="HOK Hn0"] Theorem memcpy_aligned : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    (bv_unsigned src mod 4 = 0)%Z -> (bv_unsigned dst mod 4 = 0)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa2a7c : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12 Hs4 Hd4.
    pose proof (u64_range src). pose proof (u64_range dst).
    rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
    set (m := (n mod 16)%Z).
    pose proof (Z.mod_pos_bound n 16 ltac:(lia)) as Hm16.
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (Hl16 : Z.land m 16 = 0%Z).
    { destruct B16 as [E|E]; [exact E|]. exfalso.
      pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }

    eapply (runs_trans BSEGS _ (fun r => mkst r (0xa2b9c : word) (MK 0) rom)
             (fun r => getr r 13 = at_ dst 0 /\ getr r 11 = at_ src 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ getr r 1 = ret /\ keeps regs r)).
    { destruct (al_entry regs (MK 0) H10 H11 Hs4 Hd4) as (r & R & P). exists r. split; [exact R|].
      decompose [and] P. rewrite Z.sub_0_r. repeat split; try assumption; congruence. }
    cbv beta. intros r1 (R13 & R11 & R12 & R1 & K1).

    eapply (runs_trans BSEGS _ (fun r => mkst r (0xa2bd8 : word) (MK (n - m)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al16_run r1 ret 0 R1 R11 R13 R12 ltac:(lia)) as (r & R & P). exists r.
      subst m. rewrite Z.sub_0_r in R, P. split; [exact R|]. decompose [and] P. repeat split; try assumption.
      eapply keeps_trans; eassumption. }
    cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).

    eapply (runs_trans BSEGS _ (fun r => mkst r (0xa2bf8 : word) (MK (n - m + Z.land m 8)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al8_run r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r & R & P).
      { pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).

    eapply (runs_trans BSEGS _ (fun r => mkst r (0xa2e3c : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al4_run r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia)) as (r & R & P).
      { pose proof (Z.land_nonneg m 8). lia. }
      { pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). pose proof (Z.land_nonneg m 8). lia. }
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).

    destruct (t2_run r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1) as (r & R & P).
    { pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). lia. }
    { lia. }
    exists r. split; [exact R | eapply keeps_trans; eassumption].
  Qed.

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

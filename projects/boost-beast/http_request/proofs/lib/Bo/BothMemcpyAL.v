(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib BothMemcpyBase Both_code_memcpy.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
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

  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_entry : forall regs (mem : word -> option byte),
    getr regs 10 = dst -> getr regs 11 = src ->
    (bv_unsigned src mod 4 = 0)%Z -> (bv_unsigned dst mod 4 = 0)%Z ->
    exists regs',
      msteps BSEGS2 (mkst regs (0x111ab4 : word) mem rom) (mkst regs' (0x111bd4 : word) mem rom)
      /\ getr regs' 13 = at_ dst 0 /\ getr regs' 11 = at_ src 0 /\ getr regs' 12 = getr regs 12
      /\ getr regs' 1 = getr regs 1 /\ keeps regs regs'.
  Proof.
    intros regs mem H10 H11 Hs4 Hd4.
    pose proof (u64_range src). pose proof (u64_range dst).
    eexists. split.
    - stepn F_111ab4 D_111ab4.                       (* [comment removed for export] *)
      stepb_tk F_111ab8 D_111ab8                     (* [comment removed for export] *)
        ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
      stepn F_111bc8 D_111bc8.                       (* [comment removed for export] *)
      stepn F_111bcc D_111bcc.                       (* [comment removed for export] *)
      stepb_ft F_111bd0 D_111bd0                     (* [comment removed for export] *)
        ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
      apply mst_refl.
    - repeat split; gres; rwH; rewrite ?at_0; try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b1_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    (0 <= k)%Z -> (k + 1 = n)%Z ->
    exists regs',
      msteps BSEGS2 (mkst regs (0x111eac : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    eexists. split.
    - mlbu F_111eac D_111eac k.                      (* [comment removed for export] *)
      msb F_111eb0 D_111eb0 k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
      replace (k + 1)%Z with n by lia.
      stepret F_111eb4 D_111eb4 ret ltac:(exact H1).
      apply mst_refl.
    - solve_keeps.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t2_run : forall regs (ret : word) k m,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z ->
    (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z -> (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z ->
    (0 <= k)%Z -> (n - k = Z.land m 2 + Z.land m 1)%Z ->
    exists regs',
      msteps BSEGS2 (mkst regs (0x111e74 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_111e74 D_111e74.                          (* [comment removed for export] *)
        stepb_ft F_111e78 D_111e78 ltac:(cond).           (* [comment removed for export] *)
        stepn F_111e7c D_111e7c.                          (* [comment removed for export] *)
        stepb_ft F_111e80 D_111e80 ltac:(cond).           (* [comment removed for export] *)
        stepret F_111e84 D_111e84 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS2 _ (fun r => mkst r (0x111eac : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + eexists. split.
        * stepn F_111e74 D_111e74.
          stepb_ft F_111e78 D_111e78 ltac:(cond).
          stepn F_111e7c D_111e7c.
          stepb_tk F_111e80 D_111e80 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_111e74 D_111e74.
        stepb_tk F_111e78 D_111e78 ltac:(cond).           (* [comment removed for export] *)
        mlbu F_111e88 D_111e88 k.                         (* [comment removed for export] *)
        mlbu F_111e8c D_111e8c (k + 1)%Z.                 (* [comment removed for export] *)
        stepn F_111e90 D_111e90.                          (* [comment removed for export] *)
        stepn F_111e94 D_111e94.                          (* [comment removed for export] *)
        msb F_111e98 D_111e98 k ltac:(apply sb_val_plain).          (* [comment removed for export] *)
        msb F_111e9c D_111e9c (k + 1)%Z ltac:(apply sb_val_plain).  (* [comment removed for export] *)
        stepn F_111ea0 D_111ea0.                          (* [comment removed for export] *)
        stepn F_111ea4 D_111ea4.                          (* [comment removed for export] *)
        stepb_tk F_111ea8 D_111ea8 ltac:(cond).           (* [comment removed for export] *)
        stepret F_111e84 D_111e84 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS2 _ (fun r => mkst r (0x111eac : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + eexists. split.
        * stepn F_111e74 D_111e74.
          stepb_tk F_111e78 D_111e78 ltac:(cond).
          mlbu F_111e88 D_111e88 k.
          mlbu F_111e8c D_111e8c (k + 1)%Z.
          stepn F_111e90 D_111e90.
          stepn F_111e94 D_111e94.
          msb F_111e98 D_111e98 k ltac:(apply sb_val_plain).
          msb F_111e9c D_111e9c (k + 1)%Z ltac:(apply sb_val_plain).
          stepn F_111ea0 D_111ea0.
          stepn F_111ea4 D_111ea4.
          stepb_ft F_111ea8 D_111ea8 ltac:(cond).         (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al4_run : forall regs (ret : word) k m,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps BSEGS2 (mkst regs (0x111c30 : word) (MK k) rom)
                   (mkst regs' (0x111e74 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - eexists. split.
      + stepn F_111c30 D_111c30.                          (* [comment removed for export] *)
        stepb_tk F_111c34 D_111c34 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_111c30 D_111c30.
        stepb_ft F_111c34 D_111c34 ltac:(cond).           (* [comment removed for export] *)
        mlw F_111c38 D_111c38 k.                          (* [comment removed for export] *)
        stepn F_111c3c D_111c3c.                          (* [comment removed for export] *)
        msw F_111c40 D_111c40 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).   (* [comment removed for export] *)
        stepn F_111c44 D_111c44.                          (* [comment removed for export] *)
        stepn F_111c48 D_111c48.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al8_run : forall regs (ret : word) k m e8,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
    exists regs',
      msteps BSEGS2 (mkst regs (0x111c10 : word) (MK k) rom)
                   (mkst regs' (0x111c30 : word) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - eexists. split.
      + stepn F_111c10 D_111c10.                          (* [comment removed for export] *)
        stepb_tk F_111c14 D_111c14 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_111c10 D_111c10.
        stepb_ft F_111c14 D_111c14 ltac:(cond).
        mlw F_111c18 D_111c18 k.                          (* [comment removed for export] *)
        mlw F_111c1c D_111c1c (k + 4)%Z.                  (* [comment removed for export] *)
        msw F_111c20 D_111c20 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
        msw F_111c24 D_111c24 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_111c28 D_111c28.                          (* [comment removed for export] *)
        stepn F_111c2c D_111c2c.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_loop : forall (q : nat) regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 15 ->
    (0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
    exists regs',
      msteps BSEGS2 (mkst regs (0x111be0 : word) (MK k) rom)
                   (mkst regs' (0x111c10 : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    - (* [comment removed for export] *)
      eexists. split.
      + mlw F_111be0 D_111be0 k.                          (* [comment removed for export] *)
        mlw F_111be4 D_111be4 (k + 4)%Z.                  (* [comment removed for export] *)
        mlw F_111be8 D_111be8 (k + 8)%Z.                  (* [comment removed for export] *)
        mlw F_111bec D_111bec (k + 12)%Z.                 (* [comment removed for export] *)
        stepn F_111bf0 D_111bf0.                          (* [comment removed for export] *)
        stepn F_111bf4 D_111bf4.                          (* [comment removed for export] *)
        msw F_111bf8 D_111bf8 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).          (* [comment removed for export] *)
        msw F_111bfc D_111bfc (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_111c00 D_111c00 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_111c04 D_111c04 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_111c08 D_111c08.                          (* [comment removed for export] *)
        stepb_ft F_111c0c D_111c0c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans BSEGS2 _ (fun r => mkst r (0x111be0 : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * mlw F_111be0 D_111be0 k.
          mlw F_111be4 D_111be4 (k + 4)%Z.
          mlw F_111be8 D_111be8 (k + 8)%Z.
          mlw F_111bec D_111bec (k + 12)%Z.
          stepn F_111bf0 D_111bf0.
          stepn F_111bf4 D_111bf4.
          msw F_111bf8 D_111bf8 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_111bfc D_111bfc (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_111c00 D_111c00 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_111c04 D_111c04 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          stepn F_111c08 D_111c08.
          stepb_tk F_111c0c D_111c0c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma al16_run : forall regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps BSEGS2 (mkst regs (0x111bd4 : word) (MK k) rom)
                   (mkst regs' (0x111c10 : word) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_111bd4 D_111bd4.                          (* [comment removed for export] *)
        stepb_tk F_111bd8 D_111bd8 ltac:(cond).           (* [comment removed for export] *)
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
      eapply (runs_trans BSEGS2 _ (fun r => mkst r (0x111be0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * stepn F_111bd4 D_111bd4.                        (* [comment removed for export] *)
          stepb_ft F_111bd8 D_111bd8 ltac:(cond).         (* [comment removed for export] *)
          stepn F_111bdc D_111bdc.                        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
        exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem memcpy_aligned : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    (bv_unsigned src mod 4 = 0)%Z -> (bv_unsigned dst mod 4 = 0)%Z ->
    exists regs',
      msteps BSEGS2 (mkst regs (0x111ab4 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
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
    (* [comment removed for export] *)
    eapply (runs_trans BSEGS2 _ (fun r => mkst r (0x111bd4 : word) (MK 0) rom)
             (fun r => getr r 13 = at_ dst 0 /\ getr r 11 = at_ src 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ getr r 1 = ret /\ keeps regs r)).
    { destruct (al_entry regs (MK 0) H10 H11 Hs4 Hd4) as (r & R & P). exists r. split; [exact R|].
      decompose [and] P. rewrite Z.sub_0_r. repeat split; try assumption; congruence. }
    cbv beta. intros r1 (R13 & R11 & R12 & R1 & K1).
    (* [comment removed for export] *)
    eapply (runs_trans BSEGS2 _ (fun r => mkst r (0x111c10 : word) (MK (n - m)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al16_run r1 ret 0 R1 R11 R13 R12 ltac:(lia)) as (r & R & P). exists r.
      subst m. rewrite Z.sub_0_r in R, P. split; [exact R|]. decompose [and] P. repeat split; try assumption.
      eapply keeps_trans; eassumption. }
    cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
    (* [comment removed for export] *)
    eapply (runs_trans BSEGS2 _ (fun r => mkst r (0x111c30 : word) (MK (n - m + Z.land m 8)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al8_run r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r & R & P).
      { pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
    (* [comment removed for export] *)
    eapply (runs_trans BSEGS2 _ (fun r => mkst r (0x111e74 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al4_run r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia)) as (r & R & P).
      { pose proof (Z.land_nonneg m 8). lia. }
      { pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). pose proof (Z.land_nonneg m 8). lia. }
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
    (* [comment removed for export] *)
    destruct (t2_run r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1) as (r & R & P).
    { pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). lia. }
    { lia. }
    exists r. split; [exact R | eapply keeps_trans; eassumption].
  Qed.

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

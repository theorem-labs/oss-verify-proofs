(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.coturn.FuzzStunClient.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib Require Import UbMemcpyBase UbMemcpyAL Ub_code_235f0_245f0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
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

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac sbp := apply sb_val_plain.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b4_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23e7c : word) (MK k) rom) (mkst regs' (0x23ea8 : word) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros r0 ra k a2 x1_ra x11_src x13_dst x12_a2 k_lo k_hi.
    eexists. split.
    { mlbu F_23e7c D_23e7c k.
      mlbu F_23e80 D_23e80 (k + 1)%Z.
      mlbu F_23e84 D_23e84 (k + 2)%Z.
      mlbu F_23e88 D_23e88 (k + 3)%Z.
      stepn F_23e8c D_23e8c.
      stepn F_23e90 D_23e90.
      msb F_23e94 D_23e94 k ltac:(sbp).
      msb F_23e98 D_23e98 (k + 1)%Z ltac:(sbp).
      msb F_23e9c D_23e9c (k + 2)%Z ltac:(sbp).
      msb F_23ea0 D_23ea0 (k + 3)%Z ltac:(sbp).
      stepn F_23ea4 D_23ea4.
      mk_eq. apply mst_refl. }
    post.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23e28 : word) (MK k) rom) (mkst regs' (0x23e74 : word) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros r0 ra k a2 x1_ra x11_src x13_dst x12_a2 k_lo k_hi.
    eexists. split.
    { (* eight byte loads, x14..x17 then x5 x6 x7 x28 *)
      mlbu F_23e28 D_23e28 k.
      mlbu F_23e2c D_23e2c (k + 1)%Z.
      mlbu F_23e30 D_23e30 (k + 2)%Z.
      mlbu F_23e34 D_23e34 (k + 3)%Z.
      mlbu F_23e38 D_23e38 (k + 4)%Z.
      mlbu F_23e3c D_23e3c (k + 5)%Z.
      mlbu F_23e40 D_23e40 (k + 6)%Z.
      mlbu F_23e44 D_23e44 (k + 7)%Z.
      stepn F_23e48 D_23e48.
      msb F_23e4c D_23e4c k ltac:(sbp).
      msb F_23e50 D_23e50 (k + 1)%Z ltac:(sbp).
      msb F_23e54 D_23e54 (k + 2)%Z ltac:(sbp).
      msb F_23e58 D_23e58 (k + 3)%Z ltac:(sbp).
      stepn F_23e5c D_23e5c.
      msb F_23e60 D_23e60 (k + 4)%Z ltac:(sbp).
      msb F_23e64 D_23e64 (k + 5)%Z ltac:(sbp).
      msb F_23e68 D_23e68 (k + 6)%Z ltac:(sbp).
      msb F_23e6c D_23e6c (k + 7)%Z ltac:(sbp).
      stepn F_23e70 D_23e70.
      mk_eq. apply mst_refl. }
    post.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23d94 : word) (MK k) rom) (mkst regs' (0x23e20 : word) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros r0 ra k a2 x1_ra x11_src x13_dst x12_a2 k_lo k_hi.
    eexists. split.
    { (* bytes 0..7 in, 0..3 out *)
      mlbu F_23d94 D_23d94 k.
      mlbu F_23d98 D_23d98 (k + 1)%Z.
      mlbu F_23d9c D_23d9c (k + 2)%Z.
      mlbu F_23da0 D_23da0 (k + 3)%Z.
      mlbu F_23da4 D_23da4 (k + 4)%Z.
      mlbu F_23da8 D_23da8 (k + 5)%Z.
      mlbu F_23dac D_23dac (k + 6)%Z.
      mlbu F_23db0 D_23db0 (k + 7)%Z.
      msb F_23db4 D_23db4 k ltac:(sbp).
      msb F_23db8 D_23db8 (k + 1)%Z ltac:(sbp).
      msb F_23dbc D_23dbc (k + 2)%Z ltac:(sbp).
      msb F_23dc0 D_23dc0 (k + 3)%Z ltac:(sbp).
      (* bytes 8..11 in, 4..7 out *)
      mlbu F_23dc4 D_23dc4 (k + 8)%Z.
      mlbu F_23dc8 D_23dc8 (k + 9)%Z.
      mlbu F_23dcc D_23dcc (k + 10)%Z.
      mlbu F_23dd0 D_23dd0 (k + 11)%Z.
      msb F_23dd4 D_23dd4 (k + 4)%Z ltac:(sbp).
      msb F_23dd8 D_23dd8 (k + 5)%Z ltac:(sbp).
      msb F_23ddc D_23ddc (k + 6)%Z ltac:(sbp).
      msb F_23de0 D_23de0 (k + 7)%Z ltac:(sbp).
      (* bytes 12..15 in, 8..15 out *)
      mlbu F_23de4 D_23de4 (k + 12)%Z.
      mlbu F_23de8 D_23de8 (k + 13)%Z.
      mlbu F_23dec D_23dec (k + 14)%Z.
      mlbu F_23df0 D_23df0 (k + 15)%Z.
      stepn F_23df4 D_23df4.
      msb F_23df8 D_23df8 (k + 8)%Z ltac:(sbp).
      msb F_23dfc D_23dfc (k + 9)%Z ltac:(sbp).
      msb F_23e00 D_23e00 (k + 10)%Z ltac:(sbp).
      msb F_23e04 D_23e04 (k + 11)%Z ltac:(sbp).
      stepn F_23e08 D_23e08.
      msb F_23e0c D_23e0c (k + 12)%Z ltac:(sbp).
      msb F_23e10 D_23e10 (k + 13)%Z ltac:(sbp).
      msb F_23e14 D_23e14 (k + 14)%Z ltac:(sbp).
      msb F_23e18 D_23e18 (k + 15)%Z ltac:(sbp).
      stepn F_23e1c D_23e1c.
      mk_eq. apply mst_refl. }
    post.
  Qed.

  (* [comment removed for export] *)
  Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23b50 : word) (MK k) rom) (mkst regs' (0x23ea8 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros r0 ra k m x1_ra x11_src x13_dst x12_m m_rng k_lo bit4.
    destruct (Z.eq_dec (Z.land m 4) 4) as [set4 | not_set4].
    - (* bne taken: four bytes through b4_blk *)
      destruct (b4_blk (regupd r0 14 (v_andi (getr r0 12) 4)) ra k (Z_to_bv 64 m)
                  ltac:(gres; exact x1_ra) ltac:(gres; exact x11_src)
                  ltac:(gres; exact x13_dst) ltac:(gres; exact x12_m) k_lo ltac:(lia))
        as (r2 & blk & y1 & y11 & y13 & y12 & kept_blk).
      rewrite set4. exists r2. split.
      + stepn F_23b50 D_23b50.
        stepb_tk F_23b54 D_23b54 cond.
        exact blk.
      + refine (conj y1 (conj y11 (conj y13 (conj y12 _)))).
        apply (keeps_trans _ (regupd r0 14 (v_andi (getr r0 12) 4)) _); [solve_keeps | exact kept_blk].
    - (* bne falls through, jal straight to the halfword tail *)
      assert (clear4 : (Z.land m 4 = 0)%Z) by lia.
      eexists. split.
      + stepn F_23b50 D_23b50.
        stepb_ft F_23b54 D_23b54 cond.
        stepn F_23b58 D_23b58.
        mk_eq. apply mst_refl.
      + post.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23e74 : word) (MK k) rom) (mkst regs' (0x23ea8 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros r0 ra k m x1_ra x11_src x13_dst x12_m m_rng k_lo bit4.
    destruct (Z.eq_dec (Z.land m 4) 0) as [clear4 | not_clear4].
    - (* beq taken: no word left, go to the halfword tail *)
      eexists. split.
      + stepn F_23e74 D_23e74.
        stepb_tk F_23e78 D_23e78 cond.
        mk_eq. apply mst_refl.
      + post.
    - (* beq falls into b4_blk *)
      assert (set4 : (Z.land m 4 = 4 /\ k + 4 <= n)%Z) by lia.
      destruct set4 as [set4 fits4].
      destruct (b4_blk (regupd r0 14 (v_andi (getr r0 12) 4)) ra k (Z_to_bv 64 m)
                  ltac:(gres; exact x1_ra) ltac:(gres; exact x11_src)
                  ltac:(gres; exact x13_dst) ltac:(gres; exact x12_m) k_lo fits4)
        as (r2 & blk & y1 & y11 & y13 & y12 & kept_blk).
      rewrite set4. exists r2. split.
      + stepn F_23e74 D_23e74.
        stepb_ft F_23e78 D_23e78 cond.
        exact blk.
      + refine (conj y1 (conj y11 (conj y13 (conj y12 _)))).
        apply (keeps_trans _ (regupd r0 14 (v_andi (getr r0 12) 4)) _); [solve_keeps | exact kept_blk].
  Qed.

  (* [comment removed for export] *)
  Lemma t8_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23b48 : word) (MK k) rom)
                   (mkst regs' (0x23ea8 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros r0 ra k m x1_ra x11_src x13_dst x12_m m_rng k_lo bit8 bit4 fits.
    set (r1 := regupd r0 14 (v_andi (getr r0 12) 8)).
    assert (r1_ok : getr r1 1 = ra /\ getr r1 11 = at_ src k /\ getr r1 13 = at_ dst k /\
                    getr r1 12 = Z_to_bv 64 m /\ keeps r0 r1).
    { subst r1. gres. refine (conj x1_ra (conj x11_src (conj x13_dst (conj x12_m _)))). solve_keeps. }
    destruct r1_ok as (z1 & z11 & z13 & z12 & kept1).
    destruct bit8 as [clear8 | set8].
    - (* bne falls through to t4_run *)
      destruct (t4_run r1 ra k m z1 z11 z13 z12 m_rng k_lo ltac:(lia))
        as (r2 & rest & y1 & y11 & y13 & y12 & kept_rest).
      rewrite clear8, Z.add_0_r. exists r2. split.
      + stepn F_23b48 D_23b48.
        stepb_ft F_23b4c D_23b4c cond.
        exact rest.
      + refine (conj y1 (conj y11 (conj y13 (conj y12 _)))).
        exact (keeps_trans _ _ _ kept1 kept_rest).
    - (* bne taken: eight bytes through b8_blk, then b8_tail *)
      destruct (b8_blk r1 ra k (Z_to_bv 64 m) z1 z11 z13 z12 k_lo ltac:(lia))
        as (r2 & blk & w1 & w11 & w13 & w12 & kept_blk).
      destruct (b8_tail r2 ra (k + 8) m w1 w11 w13 w12 m_rng ltac:(lia) ltac:(lia))
        as (r3 & rest & y1 & y11 & y13 & y12 & kept_rest).
      rewrite set8. exists r3. split.
      + stepn F_23b48 D_23b48.
        stepb_tk F_23b4c D_23b4c cond.
        exact (msteps_trans _ _ _ _ blk rest).
      + refine (conj y1 (conj y11 (conj y13 (conj y12 _)))).
        exact (keeps_trans _ _ _ kept1 (keeps_trans _ _ _ kept_blk kept_rest)).
  Qed.

  (* [comment removed for export] *)
  Lemma b16_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23e20 : word) (MK k) rom)
                   (mkst regs' (0x23ea8 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros r0 ra k m x1_ra x11_src x13_dst x12_m m_rng k_lo bit8 bit4 fits.
    set (r1 := regupd r0 14 (v_andi (getr r0 12) 8)).
    assert (r1_ok : getr r1 1 = ra /\ getr r1 11 = at_ src k /\ getr r1 13 = at_ dst k /\
                    getr r1 12 = Z_to_bv 64 m /\ keeps r0 r1).
    { subst r1. gres. refine (conj x1_ra (conj x11_src (conj x13_dst (conj x12_m _)))). solve_keeps. }
    destruct r1_ok as (z1 & z11 & z13 & z12 & kept1).
    destruct bit8 as [clear8 | set8].
    - (* beq taken: back to t4_run *)
      destruct (t4_run r1 ra k m z1 z11 z13 z12 m_rng k_lo ltac:(lia))
        as (r2 & rest & y1 & y11 & y13 & y12 & kept_rest).
      rewrite clear8, Z.add_0_r. exists r2. split.
      + stepn F_23e20 D_23e20.
        stepb_tk F_23e24 D_23e24 cond.
        exact rest.
      + refine (conj y1 (conj y11 (conj y13 (conj y12 _)))).
        exact (keeps_trans _ _ _ kept1 kept_rest).
    - (* beq falls into b8_blk, then b8_tail *)
      destruct (b8_blk r1 ra k (Z_to_bv 64 m) z1 z11 z13 z12 k_lo ltac:(lia))
        as (r2 & blk & w1 & w11 & w13 & w12 & kept_blk).
      destruct (b8_tail r2 ra (k + 8) m w1 w11 w13 w12 m_rng ltac:(lia) ltac:(lia))
        as (r3 & rest & y1 & y11 & y13 & y12 & kept_rest).
      rewrite set8. exists r3. split.
      + stepn F_23e20 D_23e20.
        stepb_ft F_23e24 D_23e24 cond.
        exact (msteps_trans _ _ _ _ blk rest).
      + refine (conj y1 (conj y11 (conj y13 (conj y12 _)))).
        exact (keeps_trans _ _ _ kept1 (keeps_trans _ _ _ kept_blk kept_rest)).
  Qed.

  (* [comment removed for export] *)
  Lemma t16_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 32)%Z -> (0 <= k)%Z ->
    (k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23b40 : word) (MK k) rom)
                   (mkst regs' (0x23ea8 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros r0 ra k m x1_ra x11_src x13_dst x12_m m_rng k_lo fits.
    pose proof (bits_lt32 m m_rng) as (bit16 & bit8 & bit4 & bit2 & bit1 & m_sum).
    assert (m_wide : (0 <= m < 2 ^ 64)%Z) by lia.
    set (r1 := regupd r0 14 (Z_to_bv 64 16)).
    assert (r1_ok : getr r1 1 = ra /\ getr r1 11 = at_ src k /\ getr r1 13 = at_ dst k /\
                    getr r1 12 = Z_to_bv 64 m /\ keeps r0 r1).
    { subst r1. gres. refine (conj x1_ra (conj x11_src (conj x13_dst (conj x12_m _)))). solve_keeps. }
    destruct r1_ok as (z1 & z11 & z13 & z12 & kept1).
    destruct (Z_le_gt_dec 16 m) as [from16 | below16].
    - (* bgeu taken: one sixteen-byte block, then b16_tail *)
      assert (set16 : (Z.land m 16 = 16)%Z) by lia.
      destruct (b16_blk r1 ra k (Z_to_bv 64 m) z1 z11 z13 z12 k_lo ltac:(lia))
        as (r2 & blk & w1 & w11 & w13 & w12 & kept_blk).
      destruct (b16_tail r2 ra (k + 16) m w1 w11 w13 w12 m_wide ltac:(lia) bit8 bit4 ltac:(lia))
        as (r3 & rest & y1 & y11 & y13 & y12 & kept_rest).
      rewrite set16. exists r3. split.
      + stepn F_23b40 D_23b40.
        stepb_tk F_23b44 D_23b44 cond.
        exact (msteps_trans _ _ _ _ blk rest).
      + refine (conj y1 (conj y11 (conj y13 (conj y12 _)))).
        exact (keeps_trans _ _ _ kept1 (keeps_trans _ _ _ kept_blk kept_rest)).
    - (* bgeu falls through to t8_run *)
      assert (clear16 : (Z.land m 16 = 0)%Z) by lia.
      destruct (t8_run r1 ra k m z1 z11 z13 z12 m_wide k_lo bit8 bit4 ltac:(lia))
        as (r2 & rest & y1 & y11 & y13 & y12 & kept_rest).
      rewrite clear16, Z.add_0_r. exists r2. split.
      + stepn F_23b40 D_23b40.
        stepb_ft F_23b44 D_23b44 cond.
        exact rest.
      + refine (conj y1 (conj y11 (conj y13 (conj y12 _)))).
        exact (keeps_trans _ _ _ kept1 kept_rest).
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

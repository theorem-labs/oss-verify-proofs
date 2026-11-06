(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbMemcpyBase UbMemcpyWBase UbMemcpyWAL UbMemcpyWMIS Ub_code_235f0_245f0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C3.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcW mem0 dst src n.

  #[local] Notation MK := (MW mem0 dst).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Wn _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Wnws _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Wnwd _ _ _ _ HOK.

  Ltac mlw F D jj := mlwW HOK F D jj.
  Ltac mlbu F D jj := mlbuW HOK F D jj.
  Ltac msw F D kk := mswW HOK mem0 dst F D kk.
  Ltac msb F D kk := msbW HOK mem0 dst F D kk.

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.

  Ltac post := repeat split; try solve_len; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.

  (* [comment removed for export] *)
  Lemma c3_pro : forall regs (ret : word) acc k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23b5c : word) (MK acc) rom) (mkst regs' (0x23c94 : word) (MK acc') rom)
      /\ LEN acc' ((k + 1))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 1)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 1))
      /\ getr regs' 15 = Z_to_bv 64 18 /\ keeps regs regs'.
  Proof.
    intros regs ret acc k ra_s0 a1_s0 a3_s0 a2_s0 a5_s0 k_ge0 room32 len_s0.
    (* the one-byte head takes one off the count in a2 *)
    assert (a2_step : v_addi (Z_to_bv 64 (n - k)) (-1) = Z_to_bv 64 (n - (k + 1))).
    { unfold v_addi. unorm. f_equal. lia. }
    do 2 eexists; split.
    { mlw F_23b5c D_23b5c k.
      stepn F_23b60 D_23b60.
      (* a5 = 3: the beq goes to the one-byte head at 0x23c80 *)
      stepb_tk F_23b64 D_23b64 ltac:(cond).
      msb F_23c80 D_23c80 k.
      stepn F_23c84 D_23c84.
      stepn F_23c88 D_23c88.
      stepn F_23c8c D_23c8c.
      stepn F_23c90 D_23c90.
      apply mst_refl. }
    post.
  Qed.

  (* [comment removed for export] *)
  Lemma c3_loop : forall (q : nat) regs (ret : word) acc kk ja,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 15 = Z_to_bv 64 18 ->
    (ja = kk + 15)%Z -> (1 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 3 <= n - kk < 16 * (Z.of_nat q + 1) + 19)%Z ->
    LEN acc (kk) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23c94 : word) (MK acc) rom)
                   (mkst regs' (0x23cf4 : word) (MK acc') rom)
      /\ LEN acc' ((kk + 16 * (Z.of_nat q + 1)))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 15)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    (* one trip through the body, up to the back-edge test at 0x23cf0 *)
    assert (pass : forall regs acc kk,
      getr regs 11 = at_ src (kk + 15) -> getr regs 13 = at_ dst kk ->
      getr regs 12 = Z_to_bv 64 (n - kk) -> (1 <= kk)%Z -> (kk + 19 <= n)%Z -> LEN acc kk ->
      exists regs' acc',
        msteps RSEGS (mkst regs (0x23c94 : word) (MK acc) rom) (mkst regs' (0x23cf0 : word) (MK acc') rom)
        /\ LEN acc' (kk + 16) /\ getr regs' 11 = at_ src (kk + 16 + 15)
        /\ getr regs' 13 = at_ dst (kk + 16) /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16))
        /\ getr regs' 1 = getr regs 1 /\ getr regs' 15 = getr regs 15 /\ keeps regs regs').
    { intros regs acc kk a1_s0 a3_s0 a2_s0 kk_ge1 fits19 len_s0.
      assert (a2_step : v_addi (Z_to_bv 64 (n - kk)) (-16) = Z_to_bv 64 (n - (kk + 16))).
      { unfold v_addi. unorm. f_equal. lia. }
      do 2 eexists; split.
      { stepn F_23c94 D_23c94.
        mlw F_23c98 D_23c98 (kk + 3)%Z.
        mlw F_23c9c D_23c9c (kk + 7)%Z.
        mlw F_23ca0 D_23ca0 (kk + 11)%Z.
        mlw F_23ca4 D_23ca4 (kk + 15)%Z.
        stepn F_23ca8 D_23ca8. stepn F_23cac D_23cac. stepn F_23cb0 D_23cb0.
        stepn F_23cb4 D_23cb4. stepn F_23cb8 D_23cb8. stepn F_23cbc D_23cbc.
        stepn F_23cc0 D_23cc0. stepn F_23cc4 D_23cc4. stepn F_23cc8 D_23cc8.
        stepn F_23ccc D_23ccc. stepn F_23cd0 D_23cd0.
        stepn F_23cd4 D_23cd4.
        msw F_23cd8 D_23cd8 kk.
        msw F_23cdc D_23cdc (kk + 4)%Z.
        msw F_23ce0 D_23ce0 (kk + 8)%Z.
        msw F_23ce4 D_23ce4 (kk + 12)%Z.
        stepn F_23ce8 D_23ce8.
        stepn F_23cec D_23cec.
        apply mst_refl. }
      post. }
    induction q as [|q more];
      intros regs ret acc kk ja ra_s0 a1_s0 a3_s0 a2_s0 a5_s0 ja_def kk_ge1 win len_s0; subst ja;
      destruct (pass regs acc kk a1_s0 a3_s0 a2_s0 kk_ge1 ltac:(lia) len_s0)
        as (regs1 & acc1 & run_s1 & len_s1 & a1_s1 & a3_s1 & a2_s1 & ra_s1 & a5_s1 & kept_s1).
    - (* last trip: a2 is now at most 18, so the bltu falls through *)
      exists regs1, acc1. split.
      { eapply msteps_trans; [exact run_s1|].
        stepb_ft F_23cf0 D_23cf0 ltac:(cond).
        apply mst_refl. }
      replace (kk + 16 * (Z.of_nat 0 + 1))%Z with (kk + 16)%Z by lia.
      rewrite ra_s1. repeat split; assumption.
    - (* more trips remain: the bltu goes back to 0x23c94 *)
      destruct (more regs1 ret acc1 (kk + 16)%Z (kk + 16 + 15)%Z ltac:(congruence) a1_s1 a3_s1 a2_s1
                  ltac:(congruence) eq_refl ltac:(lia) ltac:(lia) len_s1)
        as (regs2 & acc2 & run_s2 & len_s2 & ra_s2 & a1_s2 & a3_s2 & a2_s2 & kept_s2).
      exists regs2, acc2. split.
      { eapply msteps_trans; [exact run_s1|].
        stepb_tk F_23cf0 D_23cf0 ltac:(cond).
        exact run_s2. }
      replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
      repeat split; try assumption.
      apply (keeps_trans _ regs1); assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c3_exit : forall regs (ret : word) acc kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 15) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    LEN acc (kk) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23cf4 : word) (MK acc) rom)
                   (mkst regs' (0x23ea8 : word) (MK acc') rom)
      /\ LEN acc' ((kk + Z.land m 16 + Z.land m 8 + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc kk ra_s0 a1_s0 a3_s0 a2_s0 kk_ge0 short32 kk_le_n m.
    assert (m_def : m = (n - kk)%Z) by reflexivity.
    clearbody m. rewrite <- m_def in a2_s0. intros len_s0.
    destruct (bits_lt32 m ltac:(lia)) as (bit16 & bit8 & bit4 & bit2 & bit1 & m_bits).
    destruct bit16 as [no16 | has16].
    - (* m < 16: the bltu at 0x23cfc goes back to the shared 8/4-byte tail at 0x23b48 *)
      assert (head : exists regs1,
                msteps RSEGS (mkst regs (0x23cf4 : word) (MK acc) rom) (mkst regs1 (0x23b48 : word) (MK acc) rom)
                /\ getr regs1 1 = ret /\ getr regs1 11 = at_ src kk /\ getr regs1 13 = at_ dst kk
                /\ getr regs1 12 = Z_to_bv 64 m /\ keeps regs regs1).
      { eexists; split.
        { stepn F_23cf4 D_23cf4.
          stepn F_23cf8 D_23cf8.
          stepb_tk F_23cfc D_23cfc ltac:(cond).
          apply mst_refl. }
        post. }
      destruct head as (regs1 & run_s1 & ra_s1 & a1_s1 & a3_s1 & a2_s1 & kept_s1).
      destruct (t8_run mem0 dst src n rom HOK regs1 ret acc kk m ra_s1 a1_s1 a3_s1 a2_s1
                  ltac:(lia) kk_ge0 bit8 bit4 ltac:(lia) len_s0)
        as (regs2 & acc2 & run_s2 & len_s2 & ra_s2 & a1_s2 & a3_s2 & a2_s2 & kept_s2).
      exists regs2, acc2.
      rewrite no16, Z.add_0_r.
      split; [apply (msteps_trans _ _ _ _ run_s1 run_s2)|].
      repeat split; try assumption.
      apply (keeps_trans _ regs1); assumption.
    - (* 16 <= m: fall through, then jal to the 16-byte copy at 0x23d94 *)
      assert (head : exists regs1,
                msteps RSEGS (mkst regs (0x23cf4 : word) (MK acc) rom) (mkst regs1 (0x23d94 : word) (MK acc) rom)
                /\ getr regs1 1 = ret /\ getr regs1 11 = at_ src kk /\ getr regs1 13 = at_ dst kk
                /\ getr regs1 12 = Z_to_bv 64 m /\ keeps regs regs1).
      { eexists; split.
        { stepn F_23cf4 D_23cf4.
          stepn F_23cf8 D_23cf8.
          stepb_ft F_23cfc D_23cfc ltac:(cond).
          stepn F_23d00 D_23d00.
          apply mst_refl. }
        post. }
      destruct head as (regs1 & run_s1 & ra_s1 & a1_s1 & a3_s1 & a2_s1 & kept_s1).
      destruct (b16_blk mem0 dst src n rom HOK regs1 ret acc kk (Z_to_bv 64 m) ra_s1 a1_s1 a3_s1 a2_s1
                  kk_ge0 ltac:(lia) len_s0)
        as (regs2 & acc2 & run_s2 & len_s2 & ra_s2 & a1_s2 & a3_s2 & a2_s2 & kept_s2).
      destruct (b16_tail mem0 dst src n rom HOK regs2 ret acc2 (kk + 16)%Z m ra_s2 a1_s2 a3_s2 a2_s2
                  ltac:(lia) ltac:(lia) bit8 bit4 ltac:(lia) len_s2)
        as (regs3 & acc3 & run_s3 & len_s3 & ra_s3 & a1_s3 & a3_s3 & a2_s3 & kept_s3).
      exists regs3, acc3.
      rewrite has16.
      split; [apply (msteps_trans _ _ _ _ run_s1), (msteps_trans _ _ _ _ run_s2 run_s3)|].
      repeat split; try assumption.
      apply (keeps_trans _ regs2); [apply (keeps_trans _ regs1)|]; assumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c3_run : forall regs (ret : word) acc k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    LEN acc k ->
    exists regs' acc' m,
      msteps RSEGS (mkst regs (0x23b5c : word) (MK acc) rom)
                   (mkst regs' (0x23ea8 : word) (MK acc') rom)
      /\ LEN acc' ((n - (Z.land m 2 + Z.land m 1)))
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k H1 H11 H13 H12 H15 Hk Hnk HLN.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 3 <= n - (k + 1) < 16 * (Z.of_nat q + 1) + 19)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 1 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c3_pro regs ret acc k H1 H11 H13 H12 H15 Hk Hnk HLN) as (r1 & a1 & RUN1 & L1 & P1 & P11 & P13 & P12 & P15 & K1).
    destruct (c3_loop q r1 ret a1 (k + 1)%Z (k + 16)%Z P1 P11 P13 P12 P15 ltac:(lia) ltac:(lia) Hq L1) as (r2 & a2 & RUN2 & L2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, L2, Q11, Q13, Q12.
    destruct (c3_exit r2 ret a2 kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia) L2) as (r3 & a3 & RUN3 & L3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, L3, S11, S13, S12.
    exists r3, a3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in L3, S11, S13.
    split; [| split; [exact L3 | split; [lia | repeat split; try assumption]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

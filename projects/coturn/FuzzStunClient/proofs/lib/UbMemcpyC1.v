(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbMemcpyBase UbMemcpyAL UbMemcpyMIS Ub_code_235f0_245f0.
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
  Ltac m24 := eapply (merge_s24 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  Lemma c1_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23b5c : word) (MK k) rom) (mkst regs' (0x23d28 : word) (MK (k + 3)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 3)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
  Proof.
    intros r0 ra k ra_is a1_is a3_is a2_is a5_is k_ge0 room32.
    eexists. split.
    { (* first source word; a5 = 1 skips the 3-way and 2-way heads *)
      mlw F_23b5c D_23b5c k.
      stepn F_23b60 D_23b60.
      stepb_ft F_23b64 D_23b64 cond.
      stepn F_23b68 D_23b68.
      stepb_tk F_23b6c D_23b6c cond.
      (* three head bytes out of that word *)
      stepn F_23d04 D_23d04.
      stepn F_23d08 D_23d08.
      stepn F_23d0c D_23d0c.
      msb F_23d10 D_23d10 k ltac:(apply (sb_val_word0 _ _ _ _ _ HOK); lia).
      msb F_23d14 D_23d14 (k + 1)%Z ltac:(apply (sb_val_srli8 _ _ _ _ _ HOK); lia).
      msb F_23d18 D_23d18 (k + 2)%Z ltac:(apply (sb_val_srli16 _ _ _ _ _ HOK); lia).
      stepn F_23d1c D_23d1c.
      stepn F_23d20 D_23d20.
      stepn F_23d24 D_23d24.
      mk_at (k + 3)%Z. apply mst_refl. }
    gres. rwH. rewrite !at_addi.
    rewrite (v_addi_m _ 3) by (rewrite ?u_Z2bv by lia; lia).
    rewrite u_Z2bv by lia.
    refine (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj eq_refl (conj eq_refl _)))))).
    - f_equal. lia.
    - solve_keeps.
  Qed.

  (* [comment removed for export] *)
  Lemma c1_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 16 ->
    (ja = kk + 13)%Z -> (jw = kk - 3)%Z -> (3 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23d28 : word) (MK kk) rom)
                   (mkst regs' (0x23d88 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    (* one trip through the body: loop head at 23d28 up to the closing bltu at 23d84 *)
    assert (trip : forall (s0 : bvmap 5 word) (ra : word) (d : Z),
               getr s0 1 = ra -> getr s0 11 = at_ src (d + 13) -> getr s0 13 = at_ dst d ->
               getr s0 12 = Z_to_bv 64 (n - d) -> getr s0 14 = LWv (SB (d - 3) 4) ->
               getr s0 15 = Z_to_bv 64 16 -> (3 <= d)%Z -> (d + 17 <= n)%Z ->
               exists s1 : bvmap 5 word,
                 msteps RSEGS (mkst s0 (146728 : word) (MK d) rom)
                        (mkst s1 (146820 : word) (MK (d + 16)) rom) /\
                 getr s1 1 = ra /\ getr s1 11 = at_ src (d + 16 + 13) /\
                 getr s1 13 = at_ dst (d + 16) /\ getr s1 12 = Z_to_bv 64 (n - (d + 16)) /\
                 getr s1 14 = LWv (SB (d + 13) 4) /\ getr s1 15 = Z_to_bv 64 16 /\ keeps s0 s1).
    { intros s0 ra d ra_is a1_is a3_is a2_is a4_is a5_is d_lo d_room.
      eexists. split.
      - stepn F_23d28 D_23d28.
        (* four source words, at d+1, d+5, d+9, d+13 *)
        mlw F_23d2c D_23d2c (d + 1)%Z.
        mlw F_23d30 D_23d30 (d + 5)%Z.
        mlw F_23d34 D_23d34 (d + 9)%Z.
        mlw F_23d38 D_23d38 (d + 13)%Z.
        (* each output word: its low byte is the top byte of the older word (srliw 24), its upper three bytes are the low three bytes of the newer word (slli 8) *)
        stepn F_23d3c D_23d3c. stepn F_23d40 D_23d40. stepn F_23d44 D_23d44.
        stepn F_23d48 D_23d48. stepn F_23d4c D_23d4c. stepn F_23d50 D_23d50.
        stepn F_23d54 D_23d54. stepn F_23d58 D_23d58. stepn F_23d5c D_23d5c.
        stepn F_23d60 D_23d60. stepn F_23d64 D_23d64.
        stepn F_23d68 D_23d68.
        msw F_23d6c D_23d6c d ltac:(m24).
        msw F_23d70 D_23d70 (d + 4)%Z ltac:(m24).
        msw F_23d74 D_23d74 (d + 8)%Z ltac:(m24).
        msw F_23d78 D_23d78 (d + 12)%Z ltac:(m24).
        stepn F_23d7c D_23d7c.
        stepn F_23d80 D_23d80.
        mk_at (d + 16)%Z. apply mst_refl.
      - gres. rwH. rewrite !at_addi.
        rewrite v_addi_m16 by (rewrite u_Z2bv by lia; lia).
        rewrite u_Z2bv by lia.
        split; [reflexivity|]. split; [f_equal; lia|]. split; [reflexivity|].
        split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|].
        solve_keeps. }
    intro q. induction q as [|q more];
      intros regs ra kk ja jw ra_is a1_is a3_is a2_is a4_is a5_is ja_is jw_is kk_lo span;
      subst ja jw;
      destruct (trip regs ra kk ra_is a1_is a3_is a2_is a4_is a5_is kk_lo ltac:(lia))
        as (s1 & body & ra1 & a1_1 & a3_1 & a2_1 & a4_1 & a5_1 & kept1).
    - (* last trip: 16 < a2 fails, fall out of the loop *)
      assert (once : (kk + 16 * (Z.of_nat 0 + 1) = kk + 16)%Z) by lia.
      rewrite once.
      exists s1. split.
      + eapply msteps_trans; [exact body|].
        stepb_ft F_23d84 D_23d84 cond.
        apply mst_refl.
      + exact (conj ra1 (conj a1_1 (conj a3_1 (conj a2_1 kept1)))).
    - (* more to copy: bltu jumps back to the loop head *)
      destruct (more s1 ra (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z
                  ra1 a1_1 a3_1 a2_1 a4_1 a5_1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
        as (s2 & rest & ra2 & a1_2 & a3_2 & a2_2 & kept2).
      assert (shift : (kk + 16 * (Z.of_nat (S q) + 1) = kk + 16 + 16 * (Z.of_nat q + 1))%Z) by lia.
      rewrite shift.
      exists s2. split.
      + eapply msteps_trans; [exact body|].
        stepb_tk F_23d84 D_23d84 cond.
        exact rest.
      + exact (conj ra2 (conj a1_2 (conj a3_2 (conj a2_2 (keeps_trans _ _ _ kept1 kept2))))).
  Qed.

  (* [comment removed for export] *)
  Lemma c1_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps RSEGS (mkst regs (0x23d88 : word) (MK kk) rom)
                   (mkst regs' (0x23ea8 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros s0 ra kk ra_is a1_is a3_is a2_is kk_lo short kk_hi m.
    assert (m_val : m = (n - kk)%Z) by reflexivity.
    clearbody m.
    rewrite <- m_val in a2_is.
    destruct (bits_lt32 m ltac:(lia)) as (on16 & on8 & on4 & on2 & on1 & m_sum).
    (* a1 back by 13 to the next uncopied byte, a4 := 16 for the size test *)
    assert (lead : exists s1 : bvmap 5 word,
               msteps RSEGS (mkst s0 (146824 : word) (MK kk) rom) (mkst s1 (146832 : word) (MK kk) rom) /\
               getr s1 1 = ra /\ getr s1 11 = at_ src kk /\ getr s1 13 = at_ dst kk /\
               getr s1 12 = Z_to_bv 64 m /\ getr s1 14 = Z_to_bv 64 16 /\ keeps s0 s1).
    { eexists. split.
      - stepn F_23d88 D_23d88.
        stepn F_23d8c D_23d8c.
        apply mst_refl.
      - gres. rwH. rewrite at_addi.
        refine (conj eq_refl (conj _ (conj eq_refl (conj eq_refl (conj eq_refl _))))).
        + f_equal. lia.
        + solve_keeps. }
    destruct lead as (s1 & run1 & ra1 & a1_1 & a3_1 & a2_1 & a4_1 & kept1).
    destruct (Z.ltb_spec m 16) as [below16 | from16].
    - (* bltu a2, a4 taken: under 16 left, straight to the 8/4 tail at 23b48 *)
      assert (no16 : Z.land m 16 = 0%Z) by lia.
      destruct (t8_run mem0 dst src n bs rom HOK s1 ra kk m ra1 a1_1 a3_1 a2_1
                  ltac:(lia) kk_lo on8 on4 ltac:(lia))
        as (s2 & run2 & ra2 & a1_2 & a3_2 & a2_2 & kept2).
      rewrite no16, Z.add_0_r.
      exists s2. split.
      + eapply msteps_trans; [exact run1|].
        stepb_tk F_23d90 D_23d90 cond.
        exact run2.
      + exact (conj ra2 (conj a1_2 (conj a3_2 (conj a2_2 (keeps_trans _ _ _ kept1 kept2))))).
    - (* falls into the 16-byte block, then the 8/4 tail after it *)
      assert (has16 : Z.land m 16 = 16%Z) by lia.
      destruct (b16_blk mem0 dst src n bs rom HOK s1 ra kk (Z_to_bv 64 m) ra1 a1_1 a3_1 a2_1
                  kk_lo ltac:(lia))
        as (s2 & run2 & ra2 & a1_2 & a3_2 & a2_2 & kept2).
      destruct (b16_tail mem0 dst src n bs rom HOK s2 ra (kk + 16)%Z m ra2 a1_2 a3_2 a2_2
                  ltac:(lia) ltac:(lia) on8 on4 ltac:(lia))
        as (s3 & run3 & ra3 & a1_3 & a3_3 & a2_3 & kept3).
      rewrite has16.
      exists s3. split.
      + eapply msteps_trans; [exact run1|].
        stepb_ft F_23d90 D_23d90 cond.
        exact (msteps_trans _ _ _ _ run2 run3).
      + refine (conj ra3 (conj a1_3 (conj a3_3 (conj a2_3 _)))).
        exact (keeps_trans _ _ _ kept1 (keeps_trans _ _ _ kept2 kept3)).
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c1_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps RSEGS (mkst regs (0x23b5c : word) (MK k) rom)
                   (mkst regs' (0x23ea8 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros r0 ra k ra_is a1_is a3_is a2_is a5_is k_ge0 room32.
    destruct (c1_pro r0 ra k ra_is a1_is a3_is a2_is a5_is k_ge0 room32)
      as (r1 & head & ra1 & a1_1 & a3_1 & a2_1 & a4_1 & a5_1 & kept1).
    (* number of extra loop trips once three head bytes are out *)
    assert (trips : exists q : nat,
               (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
    { exists (Z.to_nat ((n - k - 4) / 16 - 1)). lia. }
    destruct trips as [q span].
    destruct (c1_loop q r1 ra (k + 3)%Z (k + 16)%Z k ra1 a1_1 a3_1 a2_1 a4_1 a5_1
                ltac:(lia) ltac:(lia) ltac:(lia) span)
      as (r2 & body & ra2 & a1_2 & a3_2 & a2_2 & kept2).
    set (e := (k + 3 + 16 * (Z.of_nat q + 1))%Z) in *.
    assert (e_val : e = (k + 3 + 16 * (Z.of_nat q + 1))%Z) by reflexivity.
    clearbody e.
    pose proof (c1_exit r2 ra e ra2 a1_2 a3_2 a2_2 ltac:(lia) ltac:(lia) ltac:(lia)) as fin.
    cbv zeta in fin.
    set (m := (n - e)%Z) in *.
    assert (m_val : m = (n - e)%Z) by reflexivity.
    clearbody m.
    destruct fin as (r3 & run_fin & ra3 & a1_3 & a3_3 & a2_3 & kept3).
    destruct (bits_lt32 m ltac:(lia)) as (_ & _ & _ & _ & _ & m_sum).
    assert (meet : (e + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z)
      by lia.
    rewrite meet in run_fin, a1_3, a3_3.
    exists r3, m.
    split; [exact (msteps_trans _ _ _ _ head (msteps_trans _ _ _ _ body run_fin))|].
    split; [lia|].
    refine (conj ra3 (conj a1_3 (conj a3_3 (conj a2_3 _)))).
    exact (keeps_trans _ _ _ kept1 (keeps_trans _ _ _ kept2 kept3)).
  Qed.

End C1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

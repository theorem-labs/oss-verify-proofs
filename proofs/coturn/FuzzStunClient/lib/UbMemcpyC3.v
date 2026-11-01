(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.coturn.FuzzStunClient.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OssFuzzTheorems.Proofs.coturn.FuzzStunClient.lib Require Import UbMemcpyBase UbMemcpyAL UbMemcpyMIS Ub_code_235f0_245f0.
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

Section C3.
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
  Ltac m8 := eapply (merge_s8 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  Lemma c3_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23b5c : word) (MK k) rom) (mkst regs' (0x23c94 : word) (MK (k + 1)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 1)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 1)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 18 /\ keeps regs regs'.
  Proof.
    intros r ra k ra_v a1_v a3_v a2_v a5_v k_lo span.
    eexists; split.
    - (* the first source word goes to a4; its low byte alone fills dst[k] *)
      mlw F_23b5c D_23b5c k.
      stepn F_23b60 D_23b60.
      stepb_tk F_23b64 D_23b64 cond.
      msb F_23c80 D_23c80 k ltac:(apply (sb_val_word0 _ _ _ _ _ HOK); lia).
      stepn F_23c84 D_23c84.
      stepn F_23c88 D_23c88.
      stepn F_23c8c D_23c8c.
      stepn F_23c90 D_23c90.
      apply mst_refl.
    - gres; rwH.
      rewrite (v_addi_m1 (Z_to_bv 64 (n - k))) by (rewrite u_Z2bv; lia).
      rewrite u_Z2bv, !at_addi by lia.
      replace (n - k - 1)%Z with (n - (k + 1))%Z by lia.
      refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl _)))))).
      solve_keeps.
  Qed.

  (* [comment removed for export] *)
  Lemma c3_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 18 ->
    (ja = kk + 15)%Z -> (jw = kk - 1)%Z -> (1 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 3 <= n - kk < 16 * (Z.of_nat q + 1) + 19)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23c94 : word) (MK kk) rom)
                   (mkst regs' (0x23cf4 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 15)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    (* One trip round the body.  The closing bltu is part of the trip: where it lands is
       read off the count that is left, so the caller only has to decide that test. *)
    assert (trip : forall (r : bvmap 5 word) (ra : word) (j : Z),
               getr r 1 = ra -> getr r 11 = at_ src (j + 15) -> getr r 13 = at_ dst j ->
               getr r 12 = Z_to_bv 64 (n - j) -> getr r 14 = LWv (SB (j - 1) 4) ->
               getr r 15 = Z_to_bv 64 18 -> (1 <= j)%Z -> (j + 19 <= n)%Z ->
               exists r' : bvmap 5 word,
                 msteps RSEGS (mkst r (146580 : word) (MK j) rom)
                   (mkst r' (if (18 <? n - (j + 16))%Z then (146580 : word) else (146676 : word))
                         (MK (j + 16)) rom) /\
                 getr r' 1 = ra /\ getr r' 11 = at_ src (j + 16 + 15) /\
                 getr r' 13 = at_ dst (j + 16) /\ getr r' 12 = Z_to_bv 64 (n - (j + 16)) /\
                 getr r' 14 = LWv (SB (j + 15) 4) /\ getr r' 15 = Z_to_bv 64 18 /\ keeps r r').
    { intros r ra j ra_v a1_v a3_v a2_v a4_v a5_v j_lo room.
      eexists; split.
      - (* four words in from src+j+3 .. src+j+15, each spliced with the one before *)
        stepn F_23c94 D_23c94.
        mlw F_23c98 D_23c98 (j + 3)%Z.
        mlw F_23c9c D_23c9c (j + 7)%Z.
        mlw F_23ca0 D_23ca0 (j + 11)%Z.
        mlw F_23ca4 D_23ca4 (j + 15)%Z.
        stepn F_23ca8 D_23ca8.
        stepn F_23cac D_23cac.
        stepn F_23cb0 D_23cb0.
        stepn F_23cb4 D_23cb4.
        stepn F_23cb8 D_23cb8.
        stepn F_23cbc D_23cbc.
        stepn F_23cc0 D_23cc0.
        stepn F_23cc4 D_23cc4.
        stepn F_23cc8 D_23cc8.
        stepn F_23ccc D_23ccc.
        stepn F_23cd0 D_23cd0.
        stepn F_23cd4 D_23cd4.
        (* four aligned words out to dst+j .. dst+j+12 *)
        msw F_23cd8 D_23cd8 j ltac:(m8).
        msw F_23cdc D_23cdc (j + 4)%Z ltac:(m8).
        msw F_23ce0 D_23ce0 (j + 8)%Z ltac:(m8).
        msw F_23ce4 D_23ce4 (j + 12)%Z ltac:(m8).
        stepn F_23ce8 D_23ce8.
        stepn F_23cec D_23cec.
        mk_eq.
        destruct (Z.ltb_spec 18 (n - (j + 16))) as [again | done].
        + stepb_tk F_23cf0 D_23cf0 ltac:(unfold v_addi; cond).
          apply mst_refl.
        + stepb_ft F_23cf0 D_23cf0 ltac:(unfold v_addi; cond).
          apply mst_refl.
      - gres; rwH.
        rewrite (v_addi_m16 (Z_to_bv 64 (n - j))) by (rewrite u_Z2bv; lia).
        rewrite u_Z2bv, !at_addi by lia.
        split; [reflexivity|]. split; [f_equal; lia|]. split; [reflexivity|].
        split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|].
        solve_keeps. }
    intro q. induction q as [|q more_trips];
      intros r ra kk ja jw ra_v a1_v a3_v a2_v a4_v a5_v ja_eq jw_eq kk_lo span; subst ja jw.
    - (* the last trip: the test fails and control falls out to 146676 *)
      destruct (trip r ra kk ra_v a1_v a3_v a2_v a4_v a5_v kk_lo ltac:(lia))
        as (r1 & run & nx_ra & nx_a1 & nx_a3 & nx_a2 & _ & _ & kept).
      replace (18 <? n - (kk + 16))%Z with false in run by (symmetry; apply Z.ltb_ge; lia).
      change (Z.of_nat 0) with 0%Z. rewrite Z.add_0_l, Z.mul_1_r.
      exists r1. exact (conj run (conj nx_ra (conj nx_a1 (conj nx_a3 (conj nx_a2 kept))))).
    - (* the test holds: back to the head, sixteen bytes on *)
      destruct (trip r ra kk ra_v a1_v a3_v a2_v a4_v a5_v kk_lo ltac:(lia))
        as (r1 & run & nx_ra & nx_a1 & nx_a3 & nx_a2 & nx_a4 & nx_a5 & kept).
      replace (18 <? n - (kk + 16))%Z with true in run by (symmetry; apply Z.ltb_lt; lia).
      destruct (more_trips r1 ra (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z
                  nx_ra nx_a1 nx_a3 nx_a2 nx_a4 nx_a5 eq_refl ltac:(lia) ltac:(lia) ltac:(lia))
        as (r2 & run' & fin_ra & fin_a1 & fin_a3 & fin_a2 & kept').
      rewrite Nat2Z.inj_succ.
      replace (kk + 16 * (Z.succ (Z.of_nat q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
      exists r2. split; [exact (msteps_trans _ _ _ _ run run')|].
      exact (conj fin_ra (conj fin_a1 (conj fin_a3 (conj fin_a2 (keeps_trans _ _ _ kept kept'))))).
  Qed.

  (* [comment removed for export] *)
  Lemma c3_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 15) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps RSEGS (mkst regs (0x23cf4 : word) (MK kk) rom)
                   (mkst regs' (0x23ea8 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros r ra kk ra_v a1_v a3_v a2_v kk_lo short kk_hi m.
    assert (m_is : m = (n - kk)%Z) by reflexivity.
    clearbody m. rewrite <- m_is in a2_v.
    destruct (bits_lt32 m ltac:(lia)) as (bit16 & bit8 & bit4 & bit2 & bit1 & m_sum).
    (* a1 is pulled back onto the next source byte; then bltu a2,16 picks the tail *)
    assert (head : exists r1 : bvmap 5 word,
               msteps RSEGS (mkst r (146676 : word) (MK kk) rom)
                 (mkst r1 (if (m <? 16)%Z then (146248 : word) else (146836 : word)) (MK kk) rom) /\
               getr r1 1 = ra /\ getr r1 11 = at_ src kk /\ getr r1 13 = at_ dst kk /\
               getr r1 12 = Z_to_bv 64 m /\ keeps r r1).
    { eexists; split.
      - stepn F_23cf4 D_23cf4.
        stepn F_23cf8 D_23cf8.
        destruct (Z.ltb_spec m 16) as [under16 | from16].
        + stepb_tk F_23cfc D_23cfc cond.
          apply mst_refl.
        + stepb_ft F_23cfc D_23cfc cond.
          stepn F_23d00 D_23d00.
          apply mst_refl.
      - gres; rwH. rewrite at_addi.
        split; [reflexivity|]. split; [f_equal; lia|].
        refine (conj eq_refl (conj eq_refl _)). solve_keeps. }
    destruct head as (r1 & run1 & hd_ra & hd_a1 & hd_a3 & hd_a2 & kept1).
    destruct (Z_lt_ge_dec m 16) as [under16 | from16].
    - (* fewer than sixteen left: the shared 8/4 tail does the rest *)
      replace (m <? 16)%Z with true in run1 by (symmetry; apply Z.ltb_lt; exact under16).
      assert (no16 : Z.land m 16 = 0%Z) by lia.
      destruct (t8_run _ _ _ _ _ rom HOK r1 ra kk m hd_ra hd_a1 hd_a3 hd_a2
                  ltac:(lia) kk_lo bit8 bit4 ltac:(lia))
        as (r2 & run2 & tl_ra & tl_a1 & tl_a3 & tl_a2 & kept2).
      rewrite no16, Z.add_0_r.
      exists r2. split; [exact (msteps_trans _ _ _ _ run1 run2)|].
      exact (conj tl_ra (conj tl_a1 (conj tl_a3 (conj tl_a2 (keeps_trans _ _ _ kept1 kept2))))).
    - (* sixteen or more: one byte-wise block of sixteen, then the 8/4 tail behind it *)
      replace (m <? 16)%Z with false in run1 by (symmetry; apply Z.ltb_ge; lia).
      assert (has16 : Z.land m 16 = 16%Z) by lia.
      destruct (b16_blk _ _ _ _ _ rom HOK r1 ra kk (Z_to_bv 64 m) hd_ra hd_a1 hd_a3 hd_a2
                  kk_lo ltac:(lia))
        as (r2 & run2 & bk_ra & bk_a1 & bk_a3 & bk_a2 & kept2).
      destruct (b16_tail _ _ _ _ _ rom HOK r2 ra (kk + 16) m bk_ra bk_a1 bk_a3 bk_a2
                  ltac:(lia) ltac:(lia) bit8 bit4 ltac:(lia))
        as (r3 & run3 & tl_ra & tl_a1 & tl_a3 & tl_a2 & kept3).
      rewrite has16.
      exists r3. split.
      + eapply msteps_trans; [exact run1|]. exact (msteps_trans _ _ _ _ run2 run3).
      + refine (conj tl_ra (conj tl_a1 (conj tl_a3 (conj tl_a2 _)))).
        exact (keeps_trans _ _ _ kept1 (keeps_trans _ _ _ kept2 kept3)).
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c3_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps RSEGS (mkst regs (0x23b5c : word) (MK k) rom)
                   (mkst regs' (0x23ea8 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros r ra k ra_v a1_v a3_v a2_v a5_v k_lo span.
    (* the q given to c3_loop: once one byte has gone ahead the word loop makes trips + 1 trips *)
    pose (trips := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (trips_z : Z.of_nat trips = ((n - k - 4) / 16 - 1)%Z) by (unfold trips; lia).
    destruct (c3_pro r ra k ra_v a1_v a3_v a2_v a5_v k_lo span)
      as (r1 & run1 & pro_ra & pro_a1 & pro_a3 & pro_a2 & pro_a4 & pro_a5 & kept1).
    destruct (c3_loop trips r1 ra (k + 1) (k + 16) k pro_ra pro_a1 pro_a3 pro_a2 pro_a4 pro_a5
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (r2 & run2 & lp_ra & lp_a1 & lp_a3 & lp_a2 & kept2).
    set (fin := (k + 1 + 16 * (Z.of_nat trips + 1))%Z) in *.
    assert (fin_is : fin = (k + 1 + 16 * (Z.of_nat trips + 1))%Z) by reflexivity.
    clearbody fin.
    destruct (c3_exit r2 ra fin lp_ra lp_a1 lp_a3 lp_a2 ltac:(lia) ltac:(lia) ltac:(lia))
      as (r3 & run3 & ex_ra & ex_a1 & ex_a3 & ex_a2 & kept3).
    destruct (bits_lt32 (n - fin) ltac:(lia)) as (_ & _ & _ & _ & _ & rest_sum).
    replace (fin + Z.land (n - fin) 16 + Z.land (n - fin) 8 + Z.land (n - fin) 4)%Z
      with (n - (Z.land (n - fin) 2 + Z.land (n - fin) 1))%Z in run3, ex_a1, ex_a3 by lia.
    exists r3, (n - fin)%Z. split.
    - eapply msteps_trans; [exact run1|]. eapply msteps_trans; [exact run2|]. exact run3.
    - split; [lia|].
      refine (conj ex_ra (conj ex_a1 (conj ex_a3 (conj ex_a2 _)))).
      eapply keeps_trans; [exact kept1|]. eapply keeps_trans; [exact kept2|]. exact kept3.
  Qed.

End C3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

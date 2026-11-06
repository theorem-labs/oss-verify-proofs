(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbMemcpyBase Ub_code_235f0_245f0.
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
      msteps RSEGS (mkst regs (0x23ae8 : word) mem rom) (mkst regs' (0x23c08 : word) mem rom)
      /\ getr regs' 13 = at_ dst 0 /\ getr regs' 11 = at_ src 0 /\ getr regs' 12 = getr regs 12
      /\ getr regs' 1 = getr regs 1 /\ keeps regs regs'.
  Proof using HOK.
    intros regs mem Ra0 Ra1 Srcal Dstal.
    pose proof (u64_range src) as Srng. pose proof (u64_range dst) as Drng.
    eexists. split.
    { stepn F_23ae8 D_23ae8.
      stepb_tk F_23aec D_23aec cond.
      stepn F_23bfc D_23bfc.
      stepn F_23c00 D_23c00.
      stepb_ft F_23c04 D_23c04 cond.
      apply mst_refl. }
    rewrite !at_0. gres. rwH.
    do 4 (split; [reflexivity|]). solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b1_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    (0 <= k)%Z -> (k + 1 = n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23ee0 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Okret Rra Ra1 Ra3 Kpos Klast.
    eexists; split.
    - mlbu F_23ee0 D_23ee0 k.
      msb F_23ee4 D_23ee4 k ltac:(apply sb_val_plain).
      stepret F_23ee8 D_23ee8 ret ltac:(exact Rra).
      rewrite Klast. apply mst_refl.
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
      msteps RSEGS (mkst regs (0x23ea8 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k m Okret Rra Ra1 Ra3 Ra2 Mrng Bit2 Bit1 Kpos Left.
    destruct Bit2 as [Two0 | Two1].
    - (* no halfword left *)
      destruct Bit1 as [One0 | One1].
      + eexists; split.
        * stepn F_23ea8 D_23ea8.
          stepb_ft F_23eac D_23eac cond.
          stepn F_23eb0 D_23eb0.
          stepb_ft F_23eb4 D_23eb4 cond.
          stepret F_23eb8 D_23eb8 ret ltac:(exact Rra).
          mk_eq. apply mst_refl.
        * solve_keeps.
      + eapply (runs_trans RSEGS _ (fun r => mkst r 147168 (MK k) rom)
                  (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
        * eexists; split.
          -- stepn F_23ea8 D_23ea8.
             stepb_ft F_23eac D_23eac cond.
             stepn F_23eb0 D_23eb0.
             stepb_tk F_23eb4 D_23eb4 cond.
             apply mst_refl.
          -- gres. refine (conj Rra (conj Ra1 (conj Ra3 _))). solve_keeps.
        * intros r1 (Q1 & Q2 & Q3 & Q4).
          destruct (b1_run r1 ret k Okret Q1 Q2 Q3 Kpos ltac:(lia)) as (r2 & Run & Kp).
          exists r2. split; [exact Run | eapply keeps_trans; eassumption].
    - (* a halfword first *)
      eapply (runs_trans RSEGS _ (fun r => mkst r 147160 (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\
                          getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists; split.
        * stepn F_23ea8 D_23ea8.
          stepb_tk F_23eac D_23eac cond.
          mlbu F_23ebc D_23ebc k.
          mlbu F_23ec0 D_23ec0 (k + 1)%Z.
          stepn F_23ec4 D_23ec4.
          stepn F_23ec8 D_23ec8.
          msb F_23ecc D_23ecc k ltac:(apply sb_val_plain).
          msb F_23ed0 D_23ed0 (k + 1)%Z ltac:(apply sb_val_plain).
          stepn F_23ed4 D_23ed4.
          mk_eq. apply mst_refl.
        * gres. rwH. rewrite !at_addi.
          do 4 (split; [reflexivity|]). solve_keeps.
      + intros r1 (Q1 & Q2 & Q3 & Q4 & Q5).
        destruct Bit1 as [One0 | One1].
        * eexists; split.
          -- stepn F_23ed8 D_23ed8.
             stepb_tk F_23edc D_23edc cond.
             stepret F_23eb8 D_23eb8 ret ltac:(exact Q1).
             mk_eq. apply mst_refl.
          -- solve_keeps.
        * eapply (runs_trans RSEGS _ (fun r => mkst r 147168 (MK (k + 2)) rom)
                    (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
          -- eexists; split.
             ++ stepn F_23ed8 D_23ed8.
                stepb_ft F_23edc D_23edc cond.
                apply mst_refl.
             ++ gres. refine (conj Q1 (conj Q2 (conj Q3 _))). solve_keeps.
          -- intros r2 (P1 & P2 & P3 & P4).
             destruct (b1_run r2 ret (k + 2) Okret P1 P2 P3 ltac:(lia) ltac:(lia)) as (r3 & Run & Kp).
             exists r3. split; [exact Run | eapply keeps_trans; eassumption].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al4_run : forall regs (ret : word) k m,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23c64 : word) (MK k) rom)
                   (mkst regs' (0x23ea8 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m Rra Ra1 Ra3 Ra2 Mrng Kpos Bit4.
    destruct Bit4 as [Four0 | [Four1 Room]].
    - rewrite Four0, Z.add_0_r.
      eexists; split.
      + stepn F_23c64 D_23c64.
        stepb_tk F_23c68 D_23c68 cond.
        apply mst_refl.
      + gres. refine (conj Rra (conj Ra1 (conj Ra3 (conj Ra2 _)))). solve_keeps.
    - rewrite Four1.
      eexists; split.
      + stepn F_23c64 D_23c64.
        stepb_ft F_23c68 D_23c68 cond.
        mlw F_23c6c D_23c6c k.
        stepn F_23c70 D_23c70.
        msw F_23c74 D_23c74 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_23c78 D_23c78.
        stepn F_23c7c D_23c7c.
        apply mst_refl.
      + gres. rwH. rewrite !at_addi.
        do 4 (split; [reflexivity|]). solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al8_run : forall regs (ret : word) k m e8,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23c44 : word) (MK k) rom)
                   (mkst regs' (0x23c64 : word) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m e8 Rra Ra1 Ra3 Ra2 Mrng Kpos Size.
    destruct Size as [[Small E0] | [Big [E8 Room]]]; subst e8.
    - rewrite Z.add_0_r.
      eexists; split.
      + stepn F_23c44 D_23c44.
        stepb_tk F_23c48 D_23c48 cond.
        apply mst_refl.
      + gres. refine (conj Rra (conj Ra1 (conj Ra3 (conj Ra2 _)))). solve_keeps.
    - eexists; split.
      + stepn F_23c44 D_23c44.
        stepb_ft F_23c48 D_23c48 cond.
        mlw F_23c4c D_23c4c k.
        mlw F_23c50 D_23c50 (k + 4)%Z.
        msw F_23c54 D_23c54 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_23c58 D_23c58 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_23c5c D_23c5c.
        stepn F_23c60 D_23c60.
        mk_eq. apply mst_refl.
      + gres. rwH. rewrite !at_addi.
        do 4 (split; [reflexivity|]). solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_loop : forall (q : nat) regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 15 ->
    (0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23c14 : word) (MK k) rom)
                   (mkst regs' (0x23c44 : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    (* one pass of the 16-byte body: loop head up to the closing bltu *)
    assert (Pass : forall (r0 : bvmap 5 word) (ret : word) (j : Z),
               getr r0 1 = ret -> getr r0 11 = at_ src j -> getr r0 13 = at_ dst j ->
               getr r0 12 = Z_to_bv 64 (n - j) -> getr r0 14 = Z_to_bv 64 15 ->
               (0 <= j)%Z -> (j + 16 <= n)%Z ->
               exists r1 : bvmap 5 word,
                 msteps RSEGS (mkst r0 146452 (MK j) rom) (mkst r1 146496 (MK (j + 16)) rom) /\
                 getr r1 1 = ret /\ getr r1 11 = at_ src (j + 16) /\ getr r1 13 = at_ dst (j + 16) /\
                 getr r1 12 = Z_to_bv 64 (n - (j + 16)) /\ getr r1 14 = Z_to_bv 64 15 /\ keeps r0 r1).
    { intros r0 ret j Rra Ra1 Ra3 Ra2 Ra4 Jpos Room.
      eexists; split.
      - mlw F_23c14 D_23c14 j.
        mlw F_23c18 D_23c18 (j + 4)%Z.
        mlw F_23c1c D_23c1c (j + 8)%Z.
        mlw F_23c20 D_23c20 (j + 12)%Z.
        stepn F_23c24 D_23c24.
        stepn F_23c28 D_23c28.
        msw F_23c2c D_23c2c j ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_23c30 D_23c30 (j + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_23c34 D_23c34 (j + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        msw F_23c38 D_23c38 (j + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
        stepn F_23c3c D_23c3c.
        mk_eq. apply mst_refl.
      - gres. rwH. rewrite !at_addi.
        do 3 (split; [reflexivity|]).
        split; [unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia|].
        split; [reflexivity|]. solve_keeps. }
    induction q as [|q IH]; intros regs ret k Rra Ra1 Ra3 Ra2 Ra4 Kpos Span.
    - destruct (Pass regs ret k Rra Ra1 Ra3 Ra2 Ra4 Kpos ltac:(lia))
        as (r1 & Run & P1 & P2 & P3 & P4 & P5 & K1).
      replace (k + 16 * (Z.of_nat 0 + 1))%Z with (k + 16)%Z by lia.
      exists r1. split.
      + eapply msteps_trans; [exact Run|].
        stepb_ft F_23c40 D_23c40 cond.
        apply mst_refl.
      + exact (conj P1 (conj P2 (conj P3 (conj P4 K1)))).
    - destruct (Pass regs ret k Rra Ra1 Ra3 Ra2 Ra4 Kpos ltac:(lia))
        as (r1 & Run & P1 & P2 & P3 & P4 & P5 & K1).
      destruct (IH r1 ret (k + 16)%Z P1 P2 P3 P4 P5 ltac:(lia) ltac:(lia))
        as (r2 & Run2 & Q1 & Q2 & Q3 & Q4 & K2).
      replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
      exists r2. split.
      + eapply msteps_trans; [exact Run|].
        stepb_tk F_23c40 D_23c40 cond.
        exact Run2.
      + refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 _)))). eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma al16_run : forall regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23c08 : word) (MK k) rom)
                   (mkst regs' (0x23c44 : word) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret k Rra Ra1 Ra3 Ra2 Kin.
    destruct (Z_lt_ge_dec (n - k) 16) as [Short | Long].
    - (* under 16 bytes left: the bltu skips the loop *)
      rewrite (Z.mod_small (n - k) 16) by lia.
      replace (n - (n - k))%Z with k by lia.
      eexists; split.
      + stepn F_23c08 D_23c08.
        stepb_tk F_23c0c D_23c0c cond.
        apply mst_refl.
      + gres. refine (conj Rra (conj Ra1 (conj Ra3 (conj Ra2 _)))). solve_keeps.
    - (* at least one 16-byte round *)
      assert (Rounds : exists q : nat, (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
      { exists (Z.to_nat ((n - k) / 16 - 1)). lia. }
      destruct Rounds as [q Qspan].
      assert (Stop : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z) by lia.
      eapply (runs_trans RSEGS _ (fun r => mkst r 146452 (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\
                          getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists; split.
        * stepn F_23c08 D_23c08.
          stepb_ft F_23c0c D_23c0c cond.
          stepn F_23c10 D_23c10.
          apply mst_refl.
        * gres. refine (conj Rra (conj Ra1 (conj Ra3 (conj Ra2 (conj eq_refl _))))). solve_keeps.
      + intros r1 (P1 & P2 & P3 & P4 & P5 & K1).
        destruct (al_loop q r1 ret k P1 P2 P3 P4 P5 ltac:(lia) Qspan)
          as (r2 & Run & Q1 & Q2 & Q3 & Q4 & K2).
        rewrite Stop in Run, Q2, Q3, Q4.
        replace (n - (n - (n - k) mod 16))%Z with ((n - k) mod 16)%Z in Q4 by lia.
        exists r2. split; [exact Run|].
        refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 _)))). eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem memcpy_aligned : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    (bv_unsigned src mod 4 = 0)%Z -> (bv_unsigned dst mod 4 = 0)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23ae8 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret Okret Rra Ra0 Ra1 Ra2 Srcal Dstal.
    (* entry checks, starting from the untouched destination MK 0 *)
    destruct (al_entry regs (MK 0) Ra0 Ra1 Srcal Dstal)
      as (s1 & Run1 & A13 & A11 & A12 & A1 & K1).
    rewrite Ra2 in A12. rewrite Rra in A1.
    rewrite <- (Z.sub_0_r n) in A12.
    (* 16-byte blocks *)
    destruct (al16_run s1 ret 0 A1 A11 A13 A12 ltac:(lia))
      as (s2 & Run2 & B1 & B11 & B13 & B12 & K2).
    rewrite Z.sub_0_r in Run2, B11, B13, B12.
    set (m := (n mod 16)%Z) in *.
    assert (Mrng : (0 <= m < 16)%Z) by (subst m; lia).
    destruct (bits_lt32 m ltac:(lia)) as (L16 & L8 & L4 & L2 & L1 & Sum).
    (* 8-byte, then 4-byte remainder *)
    destruct (al8_run s2 ret (n - m) m (Z.land m 8) B1 B11 B13 B12 ltac:(lia) ltac:(lia) ltac:(lia))
      as (s3 & Run3 & C1 & C11 & C13 & C12 & K3).
    destruct (al4_run s3 ret (n - m + Z.land m 8) m C1 C11 C13 C12 ltac:(lia) ltac:(lia) ltac:(lia))
      as (s4 & Run4 & D1 & D11 & D13 & D12 & K4).
    (* the last n mod 4 bytes (0 to 3: a halfword, then a byte, each only if needed) and the return *)
    destruct (t2_run s4 ret (n - m + Z.land m 8 + Z.land m 4) m Okret D1 D11 D13 D12
                ltac:(lia) L2 L1 ltac:(lia) ltac:(lia))
      as (s5 & Run5 & K5).
    exists s5. split.
    - rewrite <- (memk_n _ _ _ _ _ HOK).
      eapply msteps_trans; [exact Run1|].
      eapply msteps_trans; [exact Run2|].
      eapply msteps_trans; [exact Run3|].
      eapply msteps_trans; [exact Run4|].
      exact Run5.
    - eapply keeps_trans; [exact K1|].
      eapply keeps_trans; [exact K2|].
      eapply keeps_trans; [exact K3|].
      eapply keeps_trans; [exact K4|].
      exact K5.
  Qed.

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

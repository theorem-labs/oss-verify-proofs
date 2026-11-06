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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbMemcpyBase UbMemcpyWBase Ub_code_235f0_245f0.
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_entry : forall regs (mem : word -> option byte),
    getr regs 10 = dst -> getr regs 11 = src ->
    (bv_unsigned src mod 4 = 0)%Z -> (bv_unsigned dst mod 4 = 0)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x23ae8 : word) mem rom) (mkst regs' (0x23c08 : word) mem rom)
      /\ getr regs' 13 = at_ dst 0 /\ getr regs' 11 = at_ src 0 /\ getr regs' 12 = getr regs 12
      /\ getr regs' 1 = getr regs 1 /\ keeps regs regs'.
  Proof using HOK rom.  (* [comment removed for export] *)
    intros regs mem H10 H11 Hs4 Hd4.
    pose proof (u64_range src). pose proof (u64_range dst).
    eexists. split.
    - stepn F_23ae8 D_23ae8.                       (* [comment removed for export] *)
      stepb_tk F_23aec D_23aec                     (* [comment removed for export] *)
        ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
      stepn F_23bfc D_23bfc.                       (* [comment removed for export] *)
      stepn F_23c00 D_23c00.                       (* [comment removed for export] *)
      stepb_ft F_23c04 D_23c04                     (* [comment removed for export] *)
        ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
      apply mst_refl.
    - repeat split; try solve_len; gres; rwH; rewrite ?at_0; try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b1_run : forall regs (ret : word) acc k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    (0 <= k)%Z -> (k + 1 = n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23ee0 : word) (MK acc) rom) (mkst regs' ret (MK acc') rom)
      /\ LEN acc' (n)
      /\ keeps regs regs'.
  Proof.
    intros regs ret acc k Hret H1 H11 H13 Hk Hkn HLN.
    eexists. eexists. split.
    - mlbu F_23ee0 D_23ee0 k.                      (* [comment removed for export] *)
      msb F_23ee4 D_23ee4 k.   (* [comment removed for export] *)
      replace (k + 1)%Z with n by lia.
      stepret F_23ee8 D_23ee8 ret ltac:(exact H1).
      apply mst_refl.
    - first [split; [solve_len | solve_keeps] | solve_keeps].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t2_run : forall regs (ret : word) acc k m,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z ->
    (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z -> (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z ->
    (0 <= k)%Z -> (n - k = Z.land m 2 + Z.land m 1)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23ea8 : word) (MK acc) rom) (mkst regs' ret (MK acc') rom)
      /\ LEN acc' (n)
      /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem HLN.
    - (* [comment removed for export] *)
      eexists. eexists. split.
      + stepn F_23ea8 D_23ea8.                          (* [comment removed for export] *)
        stepb_ft F_23eac D_23eac ltac:(cond).           (* [comment removed for export] *)
        stepn F_23eb0 D_23eb0.                          (* [comment removed for export] *)
        stepb_ft F_23eb4 D_23eb4 ltac:(cond).           (* [comment removed for export] *)
        stepret F_23eb8 D_23eb8 ret ltac:(exact H1).
        apply mst_refl.
      + first [split; [solve_len | solve_keeps] | solve_keeps].
    - (* [comment removed for export] *)
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23ee0 : word) (MK a) rom)
                (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23ea8 D_23ea8.
          stepb_ft F_23eac D_23eac ltac:(cond).
          stepn F_23eb0 D_23eb0.
          stepb_tk F_23eb4 D_23eb4 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; [solve_len | gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret a1 k Hret R1 R11 R13 ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & L2' & K2).
        exists r2, a2. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
    - (* [comment removed for export] *)
      eexists. eexists. split.
      + stepn F_23ea8 D_23ea8.
        stepb_tk F_23eac D_23eac ltac:(cond).           (* [comment removed for export] *)
        mlbu F_23ebc D_23ebc k.                         (* [comment removed for export] *)
        mlbu F_23ec0 D_23ec0 (k + 1)%Z.                 (* [comment removed for export] *)
        stepn F_23ec4 D_23ec4.                          (* [comment removed for export] *)
        stepn F_23ec8 D_23ec8.                          (* [comment removed for export] *)
        msb F_23ecc D_23ecc k.          (* [comment removed for export] *)
        msb F_23ed0 D_23ed0 (k + 1)%Z.  (* [comment removed for export] *)
        stepn F_23ed4 D_23ed4.                          (* [comment removed for export] *)
        stepn F_23ed8 D_23ed8.                          (* [comment removed for export] *)
        stepb_tk F_23edc D_23edc ltac:(cond).           (* [comment removed for export] *)
        stepret F_23eb8 D_23eb8 ret ltac:(exact H1).
        apply mst_refl.
      + first [split; [solve_len | solve_keeps] | solve_keeps].
    - (* [comment removed for export] *)
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23ee0 : word) (MK a) rom)
                (fun r a => LEN a ((k + 2)) /\ getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23ea8 D_23ea8.
          stepb_tk F_23eac D_23eac ltac:(cond).
          mlbu F_23ebc D_23ebc k.
          mlbu F_23ec0 D_23ec0 (k + 1)%Z.
          stepn F_23ec4 D_23ec4.
          stepn F_23ec8 D_23ec8.
          msb F_23ecc D_23ecc k.
          msb F_23ed0 D_23ed0 (k + 1)%Z.
          stepn F_23ed4 D_23ed4.
          stepn F_23ed8 D_23ed8.
          stepb_ft F_23edc D_23edc ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; [solve_len | gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret a1 (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & L2' & K2).
        exists r2, a2. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al4_run : forall regs (ret : word) acc k m,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23c64 : word) (MK acc) rom)
                   (mkst regs' (0x23ea8 : word) (MK acc') rom)
      /\ LEN acc' ((k + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]] HLN.
    - eexists. eexists. split.
      + stepn F_23c64 D_23c64.                          (* [comment removed for export] *)
        stepb_tk F_23c68 D_23c68 ltac:(cond).           (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; try solve_len; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. eexists. split.
      + stepn F_23c64 D_23c64.
        stepb_ft F_23c68 D_23c68 ltac:(cond).           (* [comment removed for export] *)
        mlw F_23c6c D_23c6c k.                          (* [comment removed for export] *)
        stepn F_23c70 D_23c70.                          (* [comment removed for export] *)
        msw F_23c74 D_23c74 k.   (* [comment removed for export] *)
        stepn F_23c78 D_23c78.                          (* [comment removed for export] *)
        stepn F_23c7c D_23c7c.                          (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; try solve_len; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al8_run : forall regs (ret : word) acc k m e8,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23c44 : word) (MK acc) rom)
                   (mkst regs' (0x23c64 : word) (MK acc') rom)
      /\ LEN acc' ((k + e8))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]] HLN; subst e8.
    - eexists. eexists. split.
      + stepn F_23c44 D_23c44.                          (* [comment removed for export] *)
        stepb_tk F_23c48 D_23c48 ltac:(cond).           (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; try solve_len; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. eexists. split.
      + stepn F_23c44 D_23c44.
        stepb_ft F_23c48 D_23c48 ltac:(cond).
        mlw F_23c4c D_23c4c k.                          (* [comment removed for export] *)
        mlw F_23c50 D_23c50 (k + 4)%Z.                  (* [comment removed for export] *)
        msw F_23c54 D_23c54 k.         (* [comment removed for export] *)
        msw F_23c58 D_23c58 (k + 4)%Z. (* [comment removed for export] *)
        stepn F_23c5c D_23c5c.                          (* [comment removed for export] *)
        stepn F_23c60 D_23c60.                          (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; try solve_len; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_loop : forall (q : nat) regs (ret : word) acc k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 15 ->
    (0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23c14 : word) (MK acc) rom)
                   (mkst regs' (0x23c44 : word) (MK acc') rom)
      /\ LEN acc' ((k + 16 * (Z.of_nat q + 1)))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret acc k H1 H11 H13 H12 H14 Hk Hq HLN.
    - (* [comment removed for export] *)
      eexists. eexists. split.
      + mlw F_23c14 D_23c14 k.                          (* [comment removed for export] *)
        mlw F_23c18 D_23c18 (k + 4)%Z.                  (* [comment removed for export] *)
        mlw F_23c1c D_23c1c (k + 8)%Z.                  (* [comment removed for export] *)
        mlw F_23c20 D_23c20 (k + 12)%Z.                 (* [comment removed for export] *)
        stepn F_23c24 D_23c24.                          (* [comment removed for export] *)
        stepn F_23c28 D_23c28.                          (* [comment removed for export] *)
        msw F_23c2c D_23c2c k.          (* [comment removed for export] *)
        msw F_23c30 D_23c30 (k + 4)%Z.  (* [comment removed for export] *)
        msw F_23c34 D_23c34 (k + 8)%Z.  (* [comment removed for export] *)
        msw F_23c38 D_23c38 (k + 12)%Z. (* [comment removed for export] *)
        stepn F_23c3c D_23c3c.                          (* [comment removed for export] *)
        stepb_ft F_23c40 D_23c40 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; try solve_len; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * unfold v_addi. unorm. f_equal. lia.
        * first [split; [solve_len | solve_keeps] | solve_keeps].
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23c14 : word) (MK a) rom)
               (fun r a => LEN a ((k + 16)) /\ getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. eexists. split.
        * mlw F_23c14 D_23c14 k.
          mlw F_23c18 D_23c18 (k + 4)%Z.
          mlw F_23c1c D_23c1c (k + 8)%Z.
          mlw F_23c20 D_23c20 (k + 12)%Z.
          stepn F_23c24 D_23c24.
          stepn F_23c28 D_23c28.
          msw F_23c2c D_23c2c k.
          msw F_23c30 D_23c30 (k + 4)%Z.
          msw F_23c34 D_23c34 (k + 8)%Z.
          msw F_23c38 D_23c38 (k + 12)%Z.
          stepn F_23c3c D_23c3c.
          stepb_tk F_23c40 D_23c40 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; try solve_len; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
          -- unfold v_addi. unorm. f_equal. lia.
          -- first [split; [solve_len | solve_keeps] | solve_keeps].
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & R14 & K1).
        destruct (IH r1 ret a1 (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & P).
        exists r2, a2. split.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
          decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma al16_run : forall regs (ret : word) acc k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23c08 : word) (MK acc) rom)
                   (mkst regs' (0x23c44 : word) (MK acc') rom)
      /\ LEN acc' ((n - (n - k) mod 16))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret acc k H1 H11 H13 H12 Hk HLN.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      eexists. eexists. split.
      + stepn F_23c08 D_23c08.                          (* [comment removed for export] *)
        stepb_tk F_23c0c D_23c0c ltac:(cond).           (* [comment removed for export] *)
        replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
        apply mst_refl.
      + rewrite (Z.mod_small (n - k) 16) by lia. replace (n - (n - k))%Z with k by lia.
        repeat split; try solve_len; gres; rwH; try reflexivity. solve_keeps.
    - set (q := Z.to_nat ((n - k) / 16 - 1)).
      assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
      assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23c14 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23c08 D_23c08.                        (* [comment removed for export] *)
          stepb_ft F_23c0c D_23c0c ltac:(cond).         (* [comment removed for export] *)
          stepn F_23c10 D_23c10.                        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; try solve_len; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & R14 & K1).
        destruct (al_loop q r1 ret a1 k R1 R11 R13 R12 R14 ltac:(lia) Hq L1) as (r2 & a2 & RUN & P).
        exists r2, a2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem memcpy_alignedW : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    (bv_unsigned src mod 4 = 0)%Z -> (bv_unsigned dst mod 4 = 0)%Z ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23ae8 : word) mem0 rom) (mkst regs' ret (MK acc') rom)
      /\ LEN acc' n /\ keeps regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12 Hs4 Hd4.
    pose proof (u64_range src). pose proof (u64_range dst).
    change mem0 with (MK []).
    set (m := (n mod 16)%Z).
    pose proof (Z.mod_pos_bound n 16 ltac:(lia)) as Hm16.
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (Hl16 : Z.land m 16 = 0%Z).
    { destruct B16 as [E|E]; [exact E|]. exfalso.
      pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
    (* [comment removed for export] *)
    eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23c08 : word) (MK a) rom)
             (fun r a => LEN a 0 /\ getr r 13 = at_ dst 0 /\ getr r 11 = at_ src 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ getr r 1 = ret /\ keeps regs r)).
    { destruct (al_entry regs (MK []) H10 H11 Hs4 Hd4) as (r & R & P). exists r, []. split; [exact R|].
      decompose [and] P. rewrite Z.sub_0_r. repeat split; try assumption; try exact LEN_nil; congruence. }
    cbv beta. intros r1 a1 (L1 & R13 & R11 & R12 & R1 & K1).
    (* [comment removed for export] *)
    eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23c44 : word) (MK a) rom)
             (fun r a => LEN a (n - m) /\ getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al16_run r1 ret a1 0 R1 R11 R13 R12 ltac:(lia) L1) as (r & a & R & P). exists r, a.
      subst m. rewrite Z.sub_0_r in P. split; [exact R|]. decompose [and] P. repeat split; try assumption.
      eapply keeps_trans; eassumption. }
    cbv beta. intros r2 a2 (L2 & S1 & S11 & S13 & S12 & K2).
    (* [comment removed for export] *)
    eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23c64 : word) (MK a) rom)
             (fun r a => LEN a (n - m + Z.land m 8) /\ getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al8_run r2 ret a2 (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r & a & R & P).
      { pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
      { exact L2. }
      exists r, a. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r3 a3 (L3 & T1 & T11 & T13 & T12 & K3).
    (* [comment removed for export] *)
    eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23ea8 : word) (MK a) rom)
             (fun r a => LEN a (n - m + Z.land m 8 + Z.land m 4) /\ getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al4_run r3 ret a3 (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia)) as (r & a & R & P).
      { pose proof (Z.land_nonneg m 8). lia. }
      { pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). pose proof (Z.land_nonneg m 8). lia. }
      { exact L3. }
      exists r, a. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r4 a4 (L4 & U1 & U11 & U13 & U12 & K4).
    (* [comment removed for export] *)
    destruct (t2_run r4 ret a4 (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1) as (r & a & R & L & K).
    { pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). lia. }
    { lia. }
    { exact L4. }
    exists r, a. split; [exact R | split; [exact L | eapply keeps_trans; eassumption]].
  Qed.

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

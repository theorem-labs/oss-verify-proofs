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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbMemcpyBase UbMemcpyWBase UbMemcpyWAL Ub_code_235f0_245f0.
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

Section MIS.
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
  (* [comment removed for export] *)
  Lemma b4_blk : forall regs (ret : word) acc k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23e7c : word) (MK acc) rom) (mkst regs' (0x23ea8 : word) (MK acc') rom)
      /\ LEN acc' ((k + 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret acc k a2 H1 H11 H13 H12 Hk Hk4 HLN. eexists. eexists. split.
    - mlbu F_23e7c D_23e7c k. mlbu F_23e80 D_23e80 (k+1)%Z. mlbu F_23e84 D_23e84 (k+2)%Z. mlbu F_23e88 D_23e88 (k+3)%Z.
      stepn F_23e8c D_23e8c.                            (* [comment removed for export] *)
      stepn F_23e90 D_23e90.                            (* [comment removed for export] *)
      msb F_23e94 D_23e94 k. msb F_23e98 D_23e98 (k+1)%Z.
      msb F_23e9c D_23e9c (k+2)%Z. msb F_23ea0 D_23ea0 (k+3)%Z.
      stepn F_23ea4 D_23ea4.                            (* [comment removed for export] *)
      apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_blk : forall regs (ret : word) acc k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23e28 : word) (MK acc) rom) (mkst regs' (0x23e74 : word) (MK acc') rom)
      /\ LEN acc' ((k + 8))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret acc k a2 H1 H11 H13 H12 Hk Hk8 HLN. eexists. eexists. split.
    - mlbu F_23e28 D_23e28 k. mlbu F_23e2c D_23e2c (k+1)%Z. mlbu F_23e30 D_23e30 (k+2)%Z. mlbu F_23e34 D_23e34 (k+3)%Z.
      mlbu F_23e38 D_23e38 (k+4)%Z. mlbu F_23e3c D_23e3c (k+5)%Z. mlbu F_23e40 D_23e40 (k+6)%Z. mlbu F_23e44 D_23e44 (k+7)%Z.
      stepn F_23e48 D_23e48.                            (* [comment removed for export] *)
      msb F_23e4c D_23e4c k. msb F_23e50 D_23e50 (k+1)%Z.
      msb F_23e54 D_23e54 (k+2)%Z. msb F_23e58 D_23e58 (k+3)%Z.
      stepn F_23e5c D_23e5c.                            (* [comment removed for export] *)
      msb F_23e60 D_23e60 (k+4)%Z. msb F_23e64 D_23e64 (k+5)%Z.
      msb F_23e68 D_23e68 (k+6)%Z. msb F_23e6c D_23e6c (k+7)%Z.
      stepn F_23e70 D_23e70.                            (* [comment removed for export] *)
      apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_blk : forall regs (ret : word) acc k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23d94 : word) (MK acc) rom) (mkst regs' (0x23e20 : word) (MK acc') rom)
      /\ LEN acc' ((k + 16))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret acc k a2 H1 H11 H13 H12 Hk Hk16 HLN. eexists. eexists. split.
    - mlbu F_23d94 D_23d94 k. mlbu F_23d98 D_23d98 (k+1)%Z. mlbu F_23d9c D_23d9c (k+2)%Z. mlbu F_23da0 D_23da0 (k+3)%Z.
      mlbu F_23da4 D_23da4 (k+4)%Z. mlbu F_23da8 D_23da8 (k+5)%Z. mlbu F_23dac D_23dac (k+6)%Z. mlbu F_23db0 D_23db0 (k+7)%Z.
      msb F_23db4 D_23db4 k. msb F_23db8 D_23db8 (k+1)%Z.
      msb F_23dbc D_23dbc (k+2)%Z. msb F_23dc0 D_23dc0 (k+3)%Z.
      mlbu F_23dc4 D_23dc4 (k+8)%Z. mlbu F_23dc8 D_23dc8 (k+9)%Z. mlbu F_23dcc D_23dcc (k+10)%Z. mlbu F_23dd0 D_23dd0 (k+11)%Z.
      msb F_23dd4 D_23dd4 (k+4)%Z. msb F_23dd8 D_23dd8 (k+5)%Z.
      msb F_23ddc D_23ddc (k+6)%Z. msb F_23de0 D_23de0 (k+7)%Z.
      mlbu F_23de4 D_23de4 (k+12)%Z. mlbu F_23de8 D_23de8 (k+13)%Z. mlbu F_23dec D_23dec (k+14)%Z. mlbu F_23df0 D_23df0 (k+15)%Z.
      stepn F_23df4 D_23df4.                            (* [comment removed for export] *)
      msb F_23df8 D_23df8 (k+8)%Z. msb F_23dfc D_23dfc (k+9)%Z.
      msb F_23e00 D_23e00 (k+10)%Z. msb F_23e04 D_23e04 (k+11)%Z.
      stepn F_23e08 D_23e08.                            (* [comment removed for export] *)
      msb F_23e0c D_23e0c (k+12)%Z. msb F_23e10 D_23e10 (k+13)%Z.
      msb F_23e14 D_23e14 (k+14)%Z. msb F_23e18 D_23e18 (k+15)%Z.
      stepn F_23e1c D_23e1c.                            (* [comment removed for export] *)
      apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma t4_run : forall regs (ret : word) acc k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23b50 : word) (MK acc) rom) (mkst regs' (0x23ea8 : word) (MK acc') rom)
      /\ LEN acc' ((k + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]] HLN.
    - eexists. eexists. split.
      + stepn F_23b50 D_23b50.                          (* [comment removed for export] *)
        stepb_ft F_23b54 D_23b54 ltac:(cond).           (* [comment removed for export] *)
        stepn F_23b58 D_23b58.                          (* [comment removed for export] *)
        apply mst_refl.
      + post.
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23e7c : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23b50 D_23b50.
          stepb_tk F_23b54 D_23b54 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret a1 k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & P).
        exists r2, a2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_tail : forall regs (ret : word) acc k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23e74 : word) (MK acc) rom) (mkst regs' (0x23ea8 : word) (MK acc') rom)
      /\ LEN acc' ((k + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]] HLN.
    - eexists. eexists. split.
      + stepn F_23e74 D_23e74.                          (* [comment removed for export] *)
        stepb_tk F_23e78 D_23e78 ltac:(cond).           (* [comment removed for export] *)
        apply mst_refl.
      + post.
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23e7c : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23e74 D_23e74.
          stepb_ft F_23e78 D_23e78 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret a1 k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & P).
        exists r2, a2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t8_run : forall regs (ret : word) acc k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23b48 : word) (MK acc) rom)
                   (mkst regs' (0x23ea8 : word) (MK acc') rom)
      /\ LEN acc' ((k + Z.land m 8 + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn HLN.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - (* [comment removed for export] *)
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23b50 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23b48 D_23b48.                        (* [comment removed for export] *)
          stepb_ft F_23b4c D_23b4c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret a1 k m R1 R11 R13 R12 Hm Hk ltac:(lia) L1) as (r2 & a2 & RUN & P).
        exists r2, a2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23e28 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23b48 D_23b48.
          stepb_tk F_23b4c D_23b4c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23e74 : word) (MK a) rom)
                 (fun r a => LEN a ((k + 8)) /\ getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret a1 k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & P).
          exists r2, a2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 a2 (L2 & S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret a2 (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia) L2) as (r3 & a3 & RUN & P).
          exists r3, a3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
          split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_tail : forall regs (ret : word) acc k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23e20 : word) (MK acc) rom)
                   (mkst regs' (0x23ea8 : word) (MK acc') rom)
      /\ LEN acc' ((k + Z.land m 8 + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn HLN.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23b50 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23e20 D_23e20.                        (* [comment removed for export] *)
          stepb_tk F_23e24 D_23e24 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret a1 k m R1 R11 R13 R12 Hm Hk ltac:(lia) L1) as (r2 & a2 & RUN & P).
        exists r2, a2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23e28 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23e20 D_23e20.
          stepb_ft F_23e24 D_23e24 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23e74 : word) (MK a) rom)
                 (fun r a => LEN a ((k + 8)) /\ getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret a1 k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & P).
          exists r2, a2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 a2 (L2 & S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret a2 (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia) L2) as (r3 & a3 & RUN & P).
          exists r3, a3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t16_run : forall regs (ret : word) acc k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 32)%Z -> (0 <= k)%Z ->
    (k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23b40 : word) (MK acc) rom)
                   (mkst regs' (0x23ea8 : word) (MK acc') rom)
      /\ LEN acc' ((k + Z.land m 16 + Z.land m 8 + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m H1 H11 H13 H12 Hm Hk Hkn HLN.
    destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23b48 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23b40 D_23b40.                        (* [comment removed for export] *)
          stepb_ft F_23b44 D_23b44 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        destruct (t8_run r1 ret a1 k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia) L1) as (r2 & a2 & RUN & P).
        exists r2, a2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23d94 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23b40 D_23b40.
          stepb_tk F_23b44 D_23b44 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23e20 : word) (MK a) rom)
                 (fun r a => LEN a ((k + 16)) /\ getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret a1 k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & P).
          exists r2, a2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 a2 (L2 & S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail r2 ret a2 (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia) L2) as (r3 & a3 & RUN & P).
          exists r3, a3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

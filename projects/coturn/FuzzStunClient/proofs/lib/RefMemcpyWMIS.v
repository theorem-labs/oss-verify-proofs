(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefMemcpyBase RefMemcpyWBase RefMemcpyWAL Ref_code_235f0_2427c.
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
      msteps RSEGS (mkst regs (0x239d4 : word) (MK acc) rom) (mkst regs' (0x23a00 : word) (MK acc') rom)
      /\ LEN acc' ((k + 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret acc k a2 H1 H11 H13 H12 Hk Hk4 HLN. eexists. eexists. split.
    - mlbu F_239d4 D_239d4 k. mlbu F_239d8 D_239d8 (k+1)%Z. mlbu F_239dc D_239dc (k+2)%Z. mlbu F_239e0 D_239e0 (k+3)%Z.
      stepn F_239e4 D_239e4.                            (* [comment removed for export] *)
      stepn F_239e8 D_239e8.                            (* [comment removed for export] *)
      msb F_239ec D_239ec k. msb F_239f0 D_239f0 (k+1)%Z.
      msb F_239f4 D_239f4 (k+2)%Z. msb F_239f8 D_239f8 (k+3)%Z.
      stepn F_239fc D_239fc.                            (* [comment removed for export] *)
      apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_blk : forall regs (ret : word) acc k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23980 : word) (MK acc) rom) (mkst regs' (0x239cc : word) (MK acc') rom)
      /\ LEN acc' ((k + 8))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret acc k a2 H1 H11 H13 H12 Hk Hk8 HLN. eexists. eexists. split.
    - mlbu F_23980 D_23980 k. mlbu F_23984 D_23984 (k+1)%Z. mlbu F_23988 D_23988 (k+2)%Z. mlbu F_2398c D_2398c (k+3)%Z.
      mlbu F_23990 D_23990 (k+4)%Z. mlbu F_23994 D_23994 (k+5)%Z. mlbu F_23998 D_23998 (k+6)%Z. mlbu F_2399c D_2399c (k+7)%Z.
      stepn F_239a0 D_239a0.                            (* [comment removed for export] *)
      msb F_239a4 D_239a4 k. msb F_239a8 D_239a8 (k+1)%Z.
      msb F_239ac D_239ac (k+2)%Z. msb F_239b0 D_239b0 (k+3)%Z.
      stepn F_239b4 D_239b4.                            (* [comment removed for export] *)
      msb F_239b8 D_239b8 (k+4)%Z. msb F_239bc D_239bc (k+5)%Z.
      msb F_239c0 D_239c0 (k+6)%Z. msb F_239c4 D_239c4 (k+7)%Z.
      stepn F_239c8 D_239c8.                            (* [comment removed for export] *)
      apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_blk : forall regs (ret : word) acc k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x238ec : word) (MK acc) rom) (mkst regs' (0x23978 : word) (MK acc') rom)
      /\ LEN acc' ((k + 16))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret acc k a2 H1 H11 H13 H12 Hk Hk16 HLN. eexists. eexists. split.
    - mlbu F_238ec D_238ec k. mlbu F_238f0 D_238f0 (k+1)%Z. mlbu F_238f4 D_238f4 (k+2)%Z. mlbu F_238f8 D_238f8 (k+3)%Z.
      mlbu F_238fc D_238fc (k+4)%Z. mlbu F_23900 D_23900 (k+5)%Z. mlbu F_23904 D_23904 (k+6)%Z. mlbu F_23908 D_23908 (k+7)%Z.
      msb F_2390c D_2390c k. msb F_23910 D_23910 (k+1)%Z.
      msb F_23914 D_23914 (k+2)%Z. msb F_23918 D_23918 (k+3)%Z.
      mlbu F_2391c D_2391c (k+8)%Z. mlbu F_23920 D_23920 (k+9)%Z. mlbu F_23924 D_23924 (k+10)%Z. mlbu F_23928 D_23928 (k+11)%Z.
      msb F_2392c D_2392c (k+4)%Z. msb F_23930 D_23930 (k+5)%Z.
      msb F_23934 D_23934 (k+6)%Z. msb F_23938 D_23938 (k+7)%Z.
      mlbu F_2393c D_2393c (k+12)%Z. mlbu F_23940 D_23940 (k+13)%Z. mlbu F_23944 D_23944 (k+14)%Z. mlbu F_23948 D_23948 (k+15)%Z.
      stepn F_2394c D_2394c.                            (* [comment removed for export] *)
      msb F_23950 D_23950 (k+8)%Z. msb F_23954 D_23954 (k+9)%Z.
      msb F_23958 D_23958 (k+10)%Z. msb F_2395c D_2395c (k+11)%Z.
      stepn F_23960 D_23960.                            (* [comment removed for export] *)
      msb F_23964 D_23964 (k+12)%Z. msb F_23968 D_23968 (k+13)%Z.
      msb F_2396c D_2396c (k+14)%Z. msb F_23970 D_23970 (k+15)%Z.
      stepn F_23974 D_23974.                            (* [comment removed for export] *)
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
      msteps RSEGS (mkst regs (0x236a8 : word) (MK acc) rom) (mkst regs' (0x23a00 : word) (MK acc') rom)
      /\ LEN acc' ((k + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]] HLN.
    - eexists. eexists. split.
      + stepn F_236a8 D_236a8.                          (* [comment removed for export] *)
        stepb_ft F_236ac D_236ac ltac:(cond).           (* [comment removed for export] *)
        stepn F_236b0 D_236b0.                          (* [comment removed for export] *)
        apply mst_refl.
      + post.
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x239d4 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_236a8 D_236a8.
          stepb_tk F_236ac D_236ac ltac:(cond).         (* [comment removed for export] *)
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
      msteps RSEGS (mkst regs (0x239cc : word) (MK acc) rom) (mkst regs' (0x23a00 : word) (MK acc') rom)
      /\ LEN acc' ((k + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]] HLN.
    - eexists. eexists. split.
      + stepn F_239cc D_239cc.                          (* [comment removed for export] *)
        stepb_tk F_239d0 D_239d0 ltac:(cond).           (* [comment removed for export] *)
        apply mst_refl.
      + post.
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x239d4 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_239cc D_239cc.
          stepb_ft F_239d0 D_239d0 ltac:(cond).         (* [comment removed for export] *)
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
      msteps RSEGS (mkst regs (0x236a0 : word) (MK acc) rom)
                   (mkst regs' (0x23a00 : word) (MK acc') rom)
      /\ LEN acc' ((k + Z.land m 8 + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn HLN.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - (* [comment removed for export] *)
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x236a8 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_236a0 D_236a0.                        (* [comment removed for export] *)
          stepb_ft F_236a4 D_236a4 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret a1 k m R1 R11 R13 R12 Hm Hk ltac:(lia) L1) as (r2 & a2 & RUN & P).
        exists r2, a2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23980 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_236a0 D_236a0.
          stepb_tk F_236a4 D_236a4 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x239cc : word) (MK a) rom)
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
      msteps RSEGS (mkst regs (0x23978 : word) (MK acc) rom)
                   (mkst regs' (0x23a00 : word) (MK acc') rom)
      /\ LEN acc' ((k + Z.land m 8 + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn HLN.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x236a8 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23978 D_23978.                        (* [comment removed for export] *)
          stepb_tk F_2397c D_2397c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret a1 k m R1 R11 R13 R12 Hm Hk ltac:(lia) L1) as (r2 & a2 & RUN & P).
        exists r2, a2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23980 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23978 D_23978.
          stepb_ft F_2397c D_2397c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x239cc : word) (MK a) rom)
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
      msteps RSEGS (mkst regs (0x23698 : word) (MK acc) rom)
                   (mkst regs' (0x23a00 : word) (MK acc') rom)
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
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x236a0 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23698 D_23698.                        (* [comment removed for export] *)
          stepb_ft F_2369c D_2369c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        destruct (t8_run r1 ret a1 k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia) L1) as (r2 & a2 & RUN & P).
        exists r2, a2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x238ec : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23698 D_23698.
          stepb_tk F_2369c D_2369c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23978 : word) (MK a) rom)
                 (fun r a => LEN a ((k + 16)) /\ getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret a1 k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & P).
          exists r2, a2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 a2 (L2 & S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail r2 ret a2 (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia) L2) as (r3 & a3 & RUN & P).
          exists r3, a3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

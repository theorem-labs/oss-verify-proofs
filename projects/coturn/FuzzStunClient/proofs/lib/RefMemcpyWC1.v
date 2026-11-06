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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefMemcpyBase RefMemcpyWBase RefMemcpyWAL RefMemcpyWMIS Ref_code_235f0_2427c.
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
  Lemma c1_pro : forall regs (ret : word) acc k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x236b4 : word) (MK acc) rom) (mkst regs' (0x23880 : word) (MK acc') rom)
      /\ LEN acc' ((k + 3))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 3))
      /\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
  Proof.
    intros regs ret acc k H1 H11 H13 H12 H15 Hk Hnk HLN. eexists. eexists. split.
    - mlw F_236b4 D_236b4 k.                            (* [comment removed for export] *)
      stepn F_236b8 D_236b8.                            (* [comment removed for export] *)
      stepb_ft F_236bc D_236bc ltac:(cond).             (* [comment removed for export] *)
      stepn F_236c0 D_236c0.                            (* [comment removed for export] *)
      stepb_tk F_236c4 D_236c4 ltac:(cond).             (* [comment removed for export] *)
      stepn F_2385c D_2385c.                            (* [comment removed for export] *)
      stepn F_23860 D_23860.                            (* [comment removed for export] *)
      stepn F_23864 D_23864.                            (* [comment removed for export] *)
      msb F_23868 D_23868 k.         (* [comment removed for export] *)
      msb F_2386c D_2386c (k + 1)%Z.  (* [comment removed for export] *)
      msb F_23870 D_23870 (k + 2)%Z. (* [comment removed for export] *)
      stepn F_23874 D_23874.                            (* [comment removed for export] *)
      stepn F_23878 D_23878.                            (* [comment removed for export] *)
      stepn F_2387c D_2387c.                            (* [comment removed for export] *)
      apply mst_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c1_loop : forall (q : nat) regs (ret : word) acc kk ja,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 15 = Z_to_bv 64 16 ->
    (ja = kk + 13)%Z -> (3 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
    LEN acc (kk) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23880 : word) (MK acc) rom)
                   (mkst regs' (0x238e0 : word) (MK acc') rom)
      /\ LEN acc' ((kk + 16 * (Z.of_nat q + 1)))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret acc kk ja H1 H11 H13 H12 H15 Hja Hkk Hq HLN; subst ja.
    - eexists. eexists. split.
      + stepn F_23880 D_23880.                          (* [comment removed for export] *)
        mlw F_23884 D_23884 (kk + 1)%Z.                 (* [comment removed for export] *)
        mlw F_23888 D_23888 (kk + 5)%Z.                 (* [comment removed for export] *)
        mlw F_2388c D_2388c (kk + 9)%Z.                 (* [comment removed for export] *)
        mlw F_23890 D_23890 (kk + 13)%Z.                (* [comment removed for export] *)
        stepn F_23894 D_23894. stepn F_23898 D_23898. stepn F_2389c D_2389c.
        stepn F_238a0 D_238a0. stepn F_238a4 D_238a4. stepn F_238a8 D_238a8.
        stepn F_238ac D_238ac. stepn F_238b0 D_238b0. stepn F_238b4 D_238b4.
        stepn F_238b8 D_238b8. stepn F_238bc D_238bc.
        stepn F_238c0 D_238c0.                          (* [comment removed for export] *)
        msw F_238c4 D_238c4 kk.
        msw F_238c8 D_238c8 (kk + 4)%Z.
        msw F_238cc D_238cc (kk + 8)%Z.
        msw F_238d0 D_238d0 (kk + 12)%Z.
        stepn F_238d4 D_238d4.                          (* [comment removed for export] *)
        stepn F_238d8 D_238d8.                          (* [comment removed for export] *)
        stepb_ft F_238dc D_238dc ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        apply mst_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23880 : word) (MK a) rom)
               (fun r a => LEN a ((kk + 16)) /\ getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16))
                         /\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23880 D_23880.
          mlw F_23884 D_23884 (kk + 1)%Z.
          mlw F_23888 D_23888 (kk + 5)%Z.
          mlw F_2388c D_2388c (kk + 9)%Z.
          mlw F_23890 D_23890 (kk + 13)%Z.
          stepn F_23894 D_23894. stepn F_23898 D_23898. stepn F_2389c D_2389c.
          stepn F_238a0 D_238a0. stepn F_238a4 D_238a4. stepn F_238a8 D_238a8.
          stepn F_238ac D_238ac. stepn F_238b0 D_238b0. stepn F_238b4 D_238b4.
          stepn F_238b8 D_238b8. stepn F_238bc D_238bc.
          stepn F_238c0 D_238c0.
          msw F_238c4 D_238c4 kk.
          msw F_238c8 D_238c8 (kk + 4)%Z.
          msw F_238cc D_238cc (kk + 8)%Z.
          msw F_238d0 D_238d0 (kk + 12)%Z.
          stepn F_238d4 D_238d4.
          stepn F_238d8 D_238d8.
          stepb_tk F_238dc D_238dc ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & R15 & K1).
        destruct (IH r1 ret a1 (kk + 16)%Z (kk + 16 + 13)%Z R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & P).
        exists r2, a2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c1_exit : forall regs (ret : word) acc kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    LEN acc (kk) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x238e0 : word) (MK acc) rom)
                   (mkst regs' (0x23a00 : word) (MK acc') rom)
      /\ LEN acc' ((kk + Z.land m 16 + Z.land m 8 + Z.land m 4))
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc kk H1 H11 H13 H12 Hkk Hm Hkn m HLN. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x236a0 : word) (MK a) rom)
               (fun r a => LEN a (kk) /\ getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_238e0 D_238e0.                        (* [comment removed for export] *)
          stepn F_238e4 D_238e4.                        (* [comment removed for export] *)
          stepb_tk F_238e8 D_238e8 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ _ _ rom HOK r1 ret a1 kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia) L1) as (r2 & a2 & RUN & P).
        exists r2, a2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x238ec : word) (MK a) rom)
               (fun r a => LEN a (kk) /\ getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_238e0 D_238e0.
          stepn F_238e4 D_238e4.
          stepb_ft F_238e8 D_238e8 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23978 : word) (MK a) rom)
                 (fun r a => LEN a ((kk + 16)) /\ getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ _ _ rom HOK r1 ret a1 kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & P).
          exists r2, a2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 a2 (L2 & S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ _ _ rom HOK r2 ret a2 (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia) L2) as (r3 & a3 & RUN & P).
          exists r3, a3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c1_run : forall regs (ret : word) acc k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    LEN acc k ->
    exists regs' acc' m,
      msteps RSEGS (mkst regs (0x236b4 : word) (MK acc) rom)
                   (mkst regs' (0x23a00 : word) (MK acc') rom)
      /\ LEN acc' ((n - (Z.land m 2 + Z.land m 1)))
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret acc k H1 H11 H13 H12 H15 Hk Hnk HLN.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c1_pro regs ret acc k H1 H11 H13 H12 H15 Hk Hnk HLN) as (r1 & a1 & RUN1 & L1 & P1 & P11 & P13 & P12 & P15 & K1).
    destruct (c1_loop q r1 ret a1 (k + 3)%Z (k + 16)%Z P1 P11 P13 P12 P15 ltac:(lia) ltac:(lia) Hq L1) as (r2 & a2 & RUN2 & L2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, L2, Q11, Q13, Q12.
    destruct (c1_exit r2 ret a2 kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia) L2) as (r3 & a3 & RUN3 & L3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, L3, S11, S13, S12.
    exists r3, a3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in L3, S11, S13.
    split; [| split; [exact L3 | split; [lia | repeat split; try assumption]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

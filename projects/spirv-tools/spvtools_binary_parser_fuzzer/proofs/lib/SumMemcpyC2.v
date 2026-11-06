(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SumLib Sum_code.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim
  RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SumMemcpyBase SumMemcpyAL SumMemcpyMIS.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C2.
Context {fx : FPState}.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemcpy_words.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH segs mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ _ HOK.

  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.

  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.

  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac m16 := eapply (merge_s16 _ _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  Lemma c2_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 116) (MK k) rom) (mkst regs' (at_ base 164) (MK (k + 2)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 2)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 2)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 17 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
    - mlw (MF_074 _ _ HCODE) D_118b34 k.
      an (MF_078 _ _ HCODE) D_118b38.
      ab_ft (MF_07c _ _ HCODE) D_118b3c ltac:(cond).
      an (MF_080 _ _ HCODE) D_118b40.
      ab_ft (MF_084 _ _ HCODE) D_118b44 ltac:(cond).
      an (MF_088 _ _ HCODE) D_118b48.
      an (MF_08c _ _ HCODE) D_118b4c.
      msb (MF_090 _ _ HCODE) D_118b50 k ltac:(eapply (sb_val_word0' _ _ _ _ _ _ HOK); lia).
      msb (MF_094 _ _ HCODE) D_118b54 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ _ HOK); lia).
      an (MF_098 _ _ HCODE) D_118b58.
      an (MF_09c _ _ HCODE) D_118b5c.
      an (MF_0a0 _ _ HCODE) D_118b60.
      mk_eq. apply mst_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  Lemma c2_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 17 ->
    (ja = kk + 14)%Z -> (jw = kk - 2)%Z -> (2 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 2 <= n - kk < 16 * (Z.of_nat q + 1) + 18)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 164) (MK kk) rom)
                   (mkst regs' (at_ base 260) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 14)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - eexists. split.
      + an (MF_0a4 _ _ HCODE) D_118b64.
        mlw (MF_0a8 _ _ HCODE) D_118b68 (kk + 2)%Z.
        mlw (MF_0ac _ _ HCODE) D_118b6c (kk + 6)%Z.
        mlw (MF_0b0 _ _ HCODE) D_118b70 (kk + 10)%Z.
        mlw (MF_0b4 _ _ HCODE) D_118b74 (kk + 14)%Z.
        an (MF_0b8 _ _ HCODE) D_118b78. an (MF_0bc _ _ HCODE) D_118b7c. an (MF_0c0 _ _ HCODE) D_118b80.
        an (MF_0c4 _ _ HCODE) D_118b84. an (MF_0c8 _ _ HCODE) D_118b88. an (MF_0cc _ _ HCODE) D_118b8c.
        an (MF_0d0 _ _ HCODE) D_118b90. an (MF_0d4 _ _ HCODE) D_118b94. an (MF_0d8 _ _ HCODE) D_118b98.
        an (MF_0dc _ _ HCODE) D_118b9c. an (MF_0e0 _ _ HCODE) D_118ba0.
        an (MF_0e4 _ _ HCODE) D_118ba4.
        msw (MF_0e8 _ _ HCODE) D_118ba8 kk ltac:(m16).
        msw (MF_0ec _ _ HCODE) D_118bac (kk + 4)%Z ltac:(m16).
        msw (MF_0f0 _ _ HCODE) D_118bb0 (kk + 8)%Z ltac:(m16).
        msw (MF_0f4 _ _ HCODE) D_118bb4 (kk + 12)%Z ltac:(m16).
        an (MF_0f8 _ _ HCODE) D_118bb8.
        an (MF_0fc _ _ HCODE) D_118bbc.
        ab_ft (MF_100 _ _ HCODE) D_118bc0 ltac:(unfold v_addi; cond).
        mk_eq. apply mst_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 164) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
                         /\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
      + eexists. split.
        * an (MF_0a4 _ _ HCODE) D_118b64.
          mlw (MF_0a8 _ _ HCODE) D_118b68 (kk + 2)%Z.
          mlw (MF_0ac _ _ HCODE) D_118b6c (kk + 6)%Z.
          mlw (MF_0b0 _ _ HCODE) D_118b70 (kk + 10)%Z.
          mlw (MF_0b4 _ _ HCODE) D_118b74 (kk + 14)%Z.
          an (MF_0b8 _ _ HCODE) D_118b78. an (MF_0bc _ _ HCODE) D_118b7c. an (MF_0c0 _ _ HCODE) D_118b80.
          an (MF_0c4 _ _ HCODE) D_118b84. an (MF_0c8 _ _ HCODE) D_118b88. an (MF_0cc _ _ HCODE) D_118b8c.
          an (MF_0d0 _ _ HCODE) D_118b90. an (MF_0d4 _ _ HCODE) D_118b94. an (MF_0d8 _ _ HCODE) D_118b98.
          an (MF_0dc _ _ HCODE) D_118b9c. an (MF_0e0 _ _ HCODE) D_118ba0.
          an (MF_0e4 _ _ HCODE) D_118ba4.
          msw (MF_0e8 _ _ HCODE) D_118ba8 kk ltac:(m16).
          msw (MF_0ec _ _ HCODE) D_118bac (kk + 4)%Z ltac:(m16).
          msw (MF_0f0 _ _ HCODE) D_118bb0 (kk + 8)%Z ltac:(m16).
          msw (MF_0f4 _ _ HCODE) D_118bb4 (kk + 12)%Z ltac:(m16).
          an (MF_0f8 _ _ HCODE) D_118bb8.
          an (MF_0fc _ _ HCODE) D_118bbc.
          ab_tk (MF_100 _ _ HCODE) D_118bc0 ltac:(unfold v_addi; cond).
          mk_eq. apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Lemma c2_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 14) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps segs (mkst regs (at_ base 260) (MK kk) rom)
                   (mkst regs' (at_ base 960) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    -
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 96) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * an (MF_104 _ _ HCODE) D_118bc4.
          an (MF_108 _ _ HCODE) D_118bc8.
          ab_tk (MF_10c _ _ HCODE) D_118bcc ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ HCODE _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    -
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 684) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * an (MF_104 _ _ HCODE) D_118bc4.
          an (MF_108 _ _ HCODE) D_118bc8.
          ab_ft (MF_10c _ _ HCODE) D_118bcc ltac:(cond).
          an (MF_110 _ _ HCODE) D_118bd0.
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 824) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ HCODE _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ HCODE _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  Lemma c2_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps segs (mkst regs (at_ base 116) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

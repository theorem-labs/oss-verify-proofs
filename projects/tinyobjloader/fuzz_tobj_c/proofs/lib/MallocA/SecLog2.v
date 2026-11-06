(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SLit"; "eval"; "sv"; "valuation"; "SMd"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2"; "sm"; "sm_sv"; "M64"; "orsh"; "popc"; "smear"; "popc_sv"; "smear_sv"; "zseq"; "clz_sv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "land"; "lxor"; "modulo"; "shiftr"; "log2"; "of_nat"; "ones"; "pow"; "testbit"; "eqb"; "mul"; "@Corelib.Init.Datatypes"; "nat"; "bool"; "true"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SRL"; "ALU_AND"; "ALU_ADD"; "ALU_XOR"; "ALU_OR"; "ALU_SUB"; "M_MUL"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@Stdlib.Lists.List"; "In"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition sm (x : Z) (s : Z) : Z := Z.lor x (Z.shiftr x s).
Definition smear (x : Z) : Z := ltac2:(tb__ "0|0|
SdSdSdSdSdSdVx;Z1A2Z2A2Z4A2Z8A2Z10A2Z20A2").
Definition M64 : Z := 18446744073709551616.
Definition popc (y : Z) : Z := ltac2:(tb__ "0|1|
S1dS1aVy;S1bS1eVy;Z1A2Z5555555555555555A2A2SfA2S0S1dS18S1bR1Z3333333333333333M0A2S1bS1eR1Z2A2G0A2A2SfA2S0S1bS1dS18R1S1eR1Z4A2A2SfA2Zf0f0f0f0f0f0f0fA2S0S1eS1dS25R1Z101010101010101A2SfA2Z38A2Ty3;Ty2;Ty1;").

Fixpoint orsh (x : Z) (n : nat) : Z := match n with O => 0 | S n' => Z.lor (orsh x n') (Z.shiftr x (Z.of_nat n')) end.

Lemma orsh_testbit : ltac2:(tb__ "0|1|
S0S26S0S17Z0M0R3A2S17G0R2A2SaS7S27S23S10R5R4A2R3A2S28A3S9S26S26S8S31R1R5A2S7S27S23R6S18R4S20R1A1A2A2S28A3A2Ls;A2A2F_;F_;Fj;Fn;Fx;").
Proof.
  intros x n j Hx Hj. induction n as [|n IH]; cbn [orsh].
  - rewrite Z.bits_0. split; [discriminate | intros (s & Hs & _); lia].
  - rewrite Z.lor_spec, orb_true_iff, IH, Z.shiftr_spec by lia. split.
    + intros [(s & Hs & Hb)|Hb]; [exists s; split; [lia|exact Hb] | exists n; split; [lia|exact Hb]].
    + intros (s & Hs & Hb). destruct (Nat.eq_dec s n) as [->|Hne]; [right; exact Hb | left; exists s; split; [lia|exact Hb]].
Qed.

Lemma sm_orsh : ltac2:(tb__ "0|0|
S0S26S17Z0R2A2S7S0SdS10R3R2A2S20R2A1A2S10R3S30R2R2A2A2A3F_;Fn;Fx;").
Proof.
  intros x n Hx. apply Z.bits_inj'. intros j Hj. unfold sm.
  rewrite Z.lor_spec, Z.shiftr_spec by lia.
  destruct (Z.testbit (orsh x n) j) eqn:E1; cbn [orb].
  - symmetry. apply (proj2 (orsh_testbit x (n + n) j Hx Hj)). apply (proj1 (orsh_testbit x n j Hx Hj)) in E1 as (s & Hs & Hb). exists s. split; [lia|exact Hb].
  - destruct (Z.testbit (orsh x n) (j + Z.of_nat n)) eqn:E2.
    + symmetry. apply (proj2 (orsh_testbit x (n + n) j Hx Hj)). apply (proj1 (orsh_testbit x n (j + Z.of_nat n) Hx ltac:(lia))) in E2 as (s & Hs & Hb).
      exists (n + s)%nat. split; [lia|]. rewrite Nat2Z.inj_add. replace (j + (Z.of_nat n + Z.of_nat s)) with (j + Z.of_nat n + Z.of_nat s) by lia. exact Hb.
    + symmetry. destruct (Z.testbit (orsh x (n + n)) j) eqn:E3; [|reflexivity]. exfalso.
      apply (proj1 (orsh_testbit x (n + n) j Hx Hj)) in E3 as (s & Hs & Hb).
      destruct (Nat.lt_ge_cases s n) as [L|L].
      * assert (X : Z.testbit (orsh x n) j = true) by (apply (proj2 (orsh_testbit x n j Hx Hj)); exists s; auto). congruence.
      * assert (X : Z.testbit (orsh x n) (j + Z.of_nat n) = true).
        { apply (proj2 (orsh_testbit x n (j + Z.of_nat n) Hx ltac:(lia))). exists (s - n)%nat. split; [lia|]. rewrite Nat2Z.inj_sub by lia.
          replace (j + Z.of_nat n + (Z.of_nat s - Z.of_nat n)) with (j + Z.of_nat s) by lia. exact Hb. }
        congruence.
Qed.

Lemma smear_orsh : ltac2:(tb__ "0|0|
S0S17Z0R1A2S7S0S12R2A1S10R2U40A2A3F_;Fx;").
Proof.
  intros x Hx. unfold smear.
  replace x with (orsh x 1) at 1 by (cbn [orsh Z.of_nat]; rewrite Z.shiftr_0_r, Z.lor_0_l; reflexivity).
  change 1 with (Z.of_nat 1) at 1. rewrite (sm_orsh x 1 Hx). cbn [Nat.add].
  change 2 with (Z.of_nat 2). rewrite (sm_orsh x 2 Hx). cbn [Nat.add].
  change 4 with (Z.of_nat 4). rewrite (sm_orsh x 4 Hx). cbn [Nat.add].
  change 8 with (Z.of_nat 8). rewrite (sm_orsh x 8 Hx). cbn [Nat.add].
  change 16 with (Z.of_nat 16). rewrite (sm_orsh x 16 Hx). cbn [Nat.add].
  change 32 with (Z.of_nat 32). rewrite (sm_orsh x 32 Hx). cbn [Nat.add]. reflexivity.
Qed.

Lemma smear_ones : ltac2:(tb__ "0|0|
S0S8S19Z0R1A2S19R1S22Z2Z40A2A2A2S7S0S12R2A1S21S18S1fR2A1Z1A2A1A3F_;Fx;").
Proof.
  intros x Hx. pose proof (Z.log2_nonneg x) as L0.
  assert (L63 : Z.log2 x <= 63). { apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
  rewrite smear_orsh by lia. apply Z.bits_inj'. intros j Hj.
  rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z_lt_le_dec (Z.log2 x) j) as [A|A].
  - destruct (Z.testbit (orsh x 64) j) eqn:E; [|symmetry; apply Z.ltb_ge; lia]. exfalso.
    apply (proj1 (orsh_testbit x 64 j ltac:(lia) Hj)) in E as (s & Hs & Hb).
    rewrite Z.bits_above_log2 in Hb; [discriminate | lia | lia].
  - transitivity true; [|symmetry; apply Z.ltb_lt; lia].
    apply (proj2 (orsh_testbit x 64 j ltac:(lia) Hj)). exists (Z.to_nat (Z.log2 x - j)). split; [lia|].
    rewrite Z2Nat.id by lia. replace (j + (Z.log2 x - j)) with (Z.log2 x) by lia. apply Z.bit_log2. lia.
Qed.

Fixpoint zseq (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zseq (lo + 1) n' end.
Lemma in_zseq : ltac2:(tb__ "0|0|
S0S26S0S8S17R3R1A2S19R1S18R3S20R2A1A2A2A2S33S0R2S15R4R3A2A3F_;Fz;Fn;Flo;").
Proof.
  intros lo n. revert lo. induction n as [|n IH]; intros lo z Hz; [lia|]. cbn [zseq].
  destruct (Z.eq_dec z lo) as [->|Hne]; [left; reflexivity | right]. rewrite Nat2Z.inj_succ in Hz. apply IH. lia.
Qed.
Lemma popc_ones_all : ltac2:(tb__ "0|0|
S7S27S34S0S0S24S11S1cS21S18R1Z1A2A1ZffffffffffffffffA2A1S1aZ3fR1A2A2Lk;S15Z0U40A2A3S28A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma popc_ones : ltac2:(tb__ "0|1|
S0S8S17Z0R1A2S17R1Z3fM0A2A2S7S0S11S1cS21S18R2Z1A2A1ZffffffffffffffffA2A1S1aG0R2A2A3F_;Fk;").
Proof.
  intros k Hk. pose proof (proj1 (forallb_forall _ _) popc_ones_all k (in_zseq 0 64 k ltac:(cbn; lia))) as X. cbn beta in X.
  apply Z.eqb_eq in X. exact X.
Qed.

Theorem clzZ_log2 : ltac2:(tb__ "0|0|
S0S8S19Z0R1A2S19R1S22Z2Z40A2A2A2S7S0S11S1cS12R2A1ZffffffffffffffffA2A1S1aZ3fS1fR2A1A2A3F_;Fx;").
Proof.
  intros x Hx. rewrite smear_ones by exact Hx.
  pose proof (Z.log2_nonneg x). assert (Z.log2 x <= 63) by (apply Z.lt_succ_r; apply Z.log2_lt_pow2; lia).
  apply popc_ones. lia.
Qed.

Definition sm_sv (e : sv) (s : Z) : sv := ltac2:(tb__ "0|0|
S1S2dVe;S1S29Ve;S2Vs;A1A3A3").
Definition smear_sv (e : sv) : sv := ltac2:(tb__ "0|0|
SeSeSeSeSeSeVe;Z1A2Z2A2Z4A2Z8A2Z10A2Z20A2").
Definition popc_sv (y : sv) : sv := ltac2:(tb__ "0|1|
S1S2eVy;S1S2aS1S29Vy;S2Z1A1A3S2Z5555555555555555A1A3A3S4S1S2bS1S2aR1S2Z3333333333333333A1M0A3S1S2aS1S29R1S2Z2A1A3G0A3A3S4S1S2aS1S2bR1S1S29R1S2Z4A1A3A3S2Zf0f0f0f0f0f0f0fA1A3S4S1S29S6S2fR1S2Z101010101010101A1A3S2Z38A1A3Ty3;Ty2;Ty1;").
Definition clz_sv (e : sv) : sv := ltac2:(tb__ "0|0|
S13S1S2cS14Ve;A1S2ZffffffffffffffffA1A3A1").

Lemma xor_val_A : ltac2:(tb__ "0|2|
ScQ40M0A1M1G1S7S0SbG0S32S2cR2R1A3A2S1cSbG0R2A2SbG0R1A2A2A3Fy;Fx;").
Proof. intros. unfold alu64, alu. rewrite bv_xor_unsigned. reflexivity. Qed.

Lemma sm_sv_val : ltac2:(tb__ "0|1|
S5S4S0S8S17Z0R1A2S19R1Z40A2A2S7S0SbQ40M0S3R4SeR3R2A2A2A2SdSbG0S3R4R3A2A2R2A2A3F_;Fs;Fe;Frho;").
Proof. intros rho e s Hs. unfold sm_sv, sm. cbn [eval]. rewrite or_val_A, srl_val, Z.mod_small by lia. reflexivity. Qed.
Lemma smear_sv_val : ltac2:(tb__ "0|1|
S5S4S7S0SbQ40M0S3R2S14R1A1A2A2S12SbG0S3R2R1A2A2A1A3Fe;Frho;").
Proof. intros rho e. unfold smear_sv, smear. rewrite !sm_sv_val by lia. reflexivity. Qed.
Lemma popc_sv_val : ltac2:(tb__ "0|1|
S5S4S7S0SbQ40M0S3R2S13R1A1A2A2S11SbG0S3R2R1A2A2A1A3Fy;Frho;").
Proof.
  intros rho y. unfold popc_sv, popc, M64. cbn [eval].
  rewrite !srl_val, !mul_val, !and_val, !add_val, !srl_val, !and_val, !sub_val, !and_val, !srl_val, !u64_lit by lia.
  rewrite !(Z.mod_small 1), !(Z.mod_small 2), !(Z.mod_small 4), !(Z.mod_small 56) by lia.
  change (2 ^ 64) with 18446744073709551616. reflexivity.
Qed.
Theorem clz_sv_val : ltac2:(tb__ "0|1|
S5S4S19Z0SbQ40M0S3R2R1A2A2A2S7S0SbG0S3R3S16R2A1A2A2S1aZ3fS1fSbG0S3R3R2A2A2A1A2A3F_;Fe;Frho;").
Proof.
  intros rho e Hx. pose proof (urange (eval rho e)) as R.
  rewrite <- (clzZ_log2 (bv_unsigned (eval rho e))) by lia.
  unfold clz_sv. rewrite popc_sv_val.
  match goal with |- popc ?a = popc ?b => replace a with b; [reflexivity|] end.
  cbn [eval]. rewrite xor_val_A, smear_sv_val, u64_lit by lia. reflexivity.
Qed.

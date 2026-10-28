(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BStoreOk BShapeAlg BAgentLib BothAcct BothAcctShape BxSymExec3 BxSymExec3Sound BxSymRun3 BothPlan BothPlanSound.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import AP. Import APS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma bytes_le_to_Z_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by lia. exact IH.
Qed.

Section Sound2.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).

Lemma kread_bytes_sound : forall E M k n b off zs,
  know_ok SEGS E M k ->
  kread_bytes SEGS n k b off = Some zs ->
  0 <= estart E (SA b off) -> estart E (SA b off) + Z.of_nat n <= 2 ^ 64 ->
  exists bs, length bs = n /\ map bv_unsigned bs = zs
             /\ forall j, (j < n)%nat -> rdn SEGS M (Z_to_bv 64 (estart E (SA b off) + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros E M k n. induction n as [|n IH]; intros b off zs HK Hr Hlo Hhi.
  - cbn in Hr. injection Hr as <-. exists []. repeat split; try reflexivity. intros j Hj. lia.
  - cbn [kread_bytes] in Hr.
    destruct (kreadZ SEGS k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes SEGS n k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate]. injection Hr as <-.
    unfold kreadZ in Hz.
    pose proof (know_lookup_sound SEGS E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as KL.
    destruct (know_lookup SEGS k b off 1 false [] []) as [v scs nx| |]; try discriminate.
    destruct v as [zl| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection Hz as <-.
    assert (Hfl : flat E (SA b off) (Z.of_nat 1)) by (unfold flat; change (Z.of_nat 1) with 1; rewrite Nat2Z.inj_succ in Hhi; lia).
    destruct (KL ltac:(constructor) Hfl) as [bs1 (R1 & L1 & V1)].
    destruct bs1 as [|b0 [|? ?]]; try (cbn in L1; lia).
    destruct (IH b (off + 1) rest HK Hrest) as [bs (Lb & Mb & Rb)].
    { unfold estart in *; cbn [a_base a_off] in *. lia. }
    { unfold estart in *; cbn [a_base a_off] in *. rewrite Nat2Z.inj_succ in Hhi. lia. }
    exists (b0 :: bs). split; [cbn; lia|]. split.
    + cbn [map]. rewrite Mb. f_equal.
      cbn [edenot] in V1. apply (f_equal bv_unsigned) in V1. rewrite !u_lit64 in V1.
      unfold extz in V1. cbn [bytes_le_to_Z] in V1. rewrite Z.shiftl_0_l, Z.lor_0_r in V1.
      pose proof (u8_range b0). unfold two64 in *. rewrite Z.mod_small in V1 by lia. exact V1.
    + intros j Hj. destruct j as [|j].
      * cbn [nth]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite <- R1. reflexivity.
      * cbn [nth]. rewrite <- (Rb j) by lia. f_equal. f_equal. unfold estart; cbn [a_base a_off]. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma rdn_of_bytes1 : forall M n (a : word) bs,
  length bs = n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < n)%nat -> rdn SEGS M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
  rdn SEGS M a n = Some bs.
Proof.
  intros M n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
  - destruct bs; [reflexivity | cbn in Hlen; lia].
  - destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen.
    pose proof (Hpt 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [nth] in H0.
    destruct n as [|n'].
    + destruct bs'; [exact H0 | cbn in Hlen; lia].
    + apply rdn_cons1; [exact H0|].
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      apply IH; [lia | rewrite Hu1; lia |].
      intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
      exact (Hpt (S j) ltac:(lia)).
Qed.

Theorem node_join_sound : join_stmt SEGS A nx0 LIMIT SINV argH FS0.
Proof.
  intros b off n cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_join in Hn.
  destruct (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool eqn:Ht; [|discriminate].
  apply andb_prop in Ht as [Ht Hfx]. apply andb_prop in Ht as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
  destruct (kread_bytes SEGS n (kn cs) b off) as [zs|] eqn:Hr; [|discriminate].
  apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit (Z.of_nat n)) HK Hfx) as (F1 & F2 & F3).
  rewrite edenot_lit, u64_lit in F2, F3 by lia.
  destruct (kread_bytes_sound E _ (kn cs) n b off zs HK Hr F1 F2) as [bs (Lb & Mb & Rb)].
  apply (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))); [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH FS0); [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok]. split; [exact H8|]. split; [unfold flat; lia|].
  rewrite (rdn_of_bytes1 _ n (adenot E (SA b off)) bs Lb).
  - f_equal. cbn [edenot]. unfold word_to_le_bytes. rewrite <- Mb, zbytes_map.
    pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
    assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply Z_to_le_bytes_to_Z.
  - rewrite (flat_u E _ (Z.of_nat n)); [lia | unfold flat; lia].
  - intros j Hj. rewrite (flat_u E _ (Z.of_nat n)) by (unfold flat; lia). exact (Rb j Hj).
Qed.
End Sound2.

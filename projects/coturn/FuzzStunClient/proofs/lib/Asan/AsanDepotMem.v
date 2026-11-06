(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec SymStepR StepTac StoreOk Hoare AgentLib StartupAux RefEnframeArith RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanRPLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.SymStepR.asanreflect_fx.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Notation DEPOT := (1660120%Z).     (* [comment removed for export] *)
Notation NIDS := (5854424%Z).      (* [comment removed for export] *)
Notation MAP1 := (5854440%Z).      (* [comment removed for export] *)
Notation SSB := (1594568%Z).       (* [comment removed for export] *)
Notation IMGHI := (6324224%Z).     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cellN (m : word -> option byte) (n : nat) (a v : Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)) /\ (0 <= v < 2 ^ (8 * Z.of_nat n))%Z.
Abbreviation cell32 m a v := (cellN m 4 a v).
Abbreviation cell64 m a v := (cellN m 8 a v).

(* [comment removed for export] *)
Definition okr (m : word -> option byte) (a n : Z) : Prop :=
  forall j, (0 <= j < n)%Z -> store_ok SEGS m (Z_to_bv 64 (a + j)) 1 = true.

(* [comment removed for export] *)
Definition ovr (m : word -> option byte) (a n : Z) : Prop :=
  forall j, (0 <= j < n)%Z -> m (Z_to_bv 64 (a + j)) <> None.

Lemma okr_sub : forall m a n a' n', okr m a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> okr m a' n'.
Proof. intros m a n a' n' H H1 H2 j Hj. replace (a' + j)%Z with (a + (a' - a + j))%Z by lia. apply H. lia. Qed.

Lemma okr_grows : forall m m' a n, mem_grows m m' -> okr m a n -> okr m' a n.
Proof. intros m m' a n G H j Hj. eapply store_ok_mono; [exact G | apply H; exact Hj]. Qed.

Lemma okr_wbytes : forall m a n x bs, okr m a n -> okr (wbytes m x bs) a n.
Proof. intros. eapply okr_grows; [apply wbytes_grows | assumption]. Qed.

Lemma okr_store_ok : forall m a (n : nat), (0 <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z ->
  okr m a (Z.of_nat n) -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof. intros m a n Ha Hn H. apply store_ok_bytes; [exact Ha | exact Hn | exact H]. Qed.

Lemma ovr_okr : forall m a n, ovr m a n -> okr m a n.
Proof.
  intros m a n H j Hj. cbn [store_ok]. unfold wview.
  destruct (m (Z_to_bv 64 (a + j))) eqn:E; [reflexivity|]. exfalso. exact (H j Hj E).
Qed.

Lemma ovr_grows : forall m m' a n, mem_grows m m' -> ovr m a n -> ovr m' a n.
Proof. intros m m' a n G H j Hj. apply G. apply H. exact Hj. Qed.

Lemma ovr_sub : forall m a n a' n', ovr m a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> ovr m a' n'.
Proof. intros m a n a' n' H H1 H2 j Hj. replace (a' + j)%Z with (a + (a' - a + j))%Z by lia. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma ovr_rdn : forall k m a, (0 <= a)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z -> ovr m a (Z.of_nat k) ->
  exists bs, rdn SEGS m (Z_to_bv 64 a) k = Some bs /\ length bs = k.
Proof.
  induction k as [|k IH]; intros m a Ha Hk H.
  - exists []. split; reflexivity.
  - cbn [rdn]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
    + destruct (IH m (a + 1)%Z ltac:(lia) ltac:(lia)) as (bs & Hbs & Hl).
      { intros j Hj. replace (a + 1 + j)%Z with (a + (1 + j))%Z by lia. apply H. lia. }
      rewrite zbv_add1, Hbs. exists (b :: bs). split; [reflexivity | cbn; lia].
    + exfalso. apply (H 0%Z ltac:(lia)). rewrite Z.add_0_r. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cellN_len : forall m n a v, cellN m n a v -> length (word_to_le_bytes n (Z_to_bv 64 v)) = n.
Proof. intros. apply length_N_to_le_bytes. Qed.

Lemma bytes_le_cell : forall n v, (0 <= v < 2 ^ (8 * Z.of_nat n))%Z -> (n <= 8)%nat ->
  bytes_le_to_Z (word_to_le_bytes n (Z_to_bv 64 v)) = v.
Proof.
  intros n v Hv Hn. rewrite bytes_le_N. rewrite u64_lit.
  - apply Z.mod_small. exact Hv.
  - assert ((2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma v_lw_lit : forall t, (0 <= t < 2 ^ 31)%Z -> v_lw (Z_to_bv 64 t) = Z_to_bv 64 t.
Proof. intros t Ht. apply v_lw_small. rewrite u64_lit by lia. lia. Qed.

(* [comment removed for export] *)
Lemma load_result_w : forall t, (0 <= t < 2 ^ 31)%Z ->
  load_result SZ4 true (word_to_le_bytes 4 (Z_to_bv 64 t)) = Z_to_bv 64 t.
Proof.
  intros t Ht. cbn [load_result].
  rewrite (le_word_v _ (Z_to_bv 64 t)) by (rewrite bytes_le_cell by (first [lia | cbn; lia]); symmetry; apply u64_lit; lia).
  rewrite b_lw_val. apply v_lw_lit. exact Ht.
Qed.

Lemma load_result_d : forall t, (0 <= t < 2 ^ 64)%Z ->
  load_result SZ8 true (word_to_le_bytes 8 (Z_to_bv 64 t)) = Z_to_bv 64 t.
Proof.
  intros t Ht. cbn [load_result].
  rewrite (le_word_v _ (Z_to_bv 64 t)) by (rewrite bytes_le_to_Z_8; reflexivity).
  apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. rewrite Z_to_bv_unsigned. apply bv_wrap_bv_wrap. lia.
Qed.

Lemma u32_extract : forall t, (0 <= t < 2 ^ 32)%Z ->
  bv_unsigned (bv_extract 0 32 (le_bytes_to_word (word_to_le_bytes 4 (Z_to_bv 64 t)))) = t.
Proof.
  intros t Ht. rewrite (le_word_v _ (Z_to_bv 64 t)) by (rewrite bytes_le_cell by (first [lia | cbn; lia]); symmetry; apply u64_lit; lia).
  rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite (Z.mod_small t (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma u_low32 : forall s : word, bv_unsigned (low32 s) = (bv_unsigned s mod 2 ^ 32)%Z.
Proof. intros s. unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r. reflexivity. Qed.

Lemma Z_to_le_bytes_mod : forall n z, Z_to_le_bytes n z = Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros z; [reflexivity|].
  assert (HK : (2 ^ (8 * Z.of_nat (S n)) = 2 ^ 8 * 2 ^ (8 * Z.of_nat n))%Z)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  cbn [Z_to_le_bytes]. f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8)%Z.
    symmetry. apply Z.mod_mod_divide. exists (2 ^ (8 * Z.of_nat n))%Z. rewrite HK. lia.
  - rewrite (IH (Z.shiftr z 8)), (IH (Z.shiftr (z mod _) 8)). f_equal.
    rewrite !Z.shiftr_div_pow2 by lia. rewrite HK.
    rewrite Z.rem_mul_r by lia.
    rewrite (Z.mul_comm (2 ^ 8) ((z / 2 ^ 8) mod 2 ^ (8 * Z.of_nat n))).
    rewrite Z.div_add by lia. rewrite (Z.div_small (z mod 2 ^ 8)) by (apply Z.mod_pos_bound; lia).
    rewrite Z.add_0_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma amo_add_w_bytes : forall t (s : word), (0 <= t < 2 ^ 32)%Z ->
  amo_store_bytes AMO_ADD AW (word_to_le_bytes 4 (Z_to_bv 64 t)) s
  = word_to_le_bytes 4 (Z_to_bv 64 ((t + bv_unsigned s) mod 2 ^ 32)).
Proof.
  intros t s Ht. unfold amo_store_bytes. cbn [amo_val].
  rewrite bv_add_unsigned. rewrite u32_extract by exact Ht. rewrite u_low32.
  unfold word_to_le_bytes.
  rewrite (u64_lit ((t + bv_unsigned s) mod 2 ^ 32)) by (pose proof (Z.mod_pos_bound (t + bv_unsigned s) (2 ^ 32)); lia).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z.
  f_equal. apply Zplus_mod_idemp_r.
Qed.

Lemma amo_add_d_bytes : forall t (s : word), (0 <= t < 2 ^ 64)%Z ->
  amo_store_bytes AMO_ADD AD (word_to_le_bytes 8 (Z_to_bv 64 t)) s
  = word_to_le_bytes 8 (Z_to_bv 64 ((t + bv_unsigned s) mod 2 ^ 64)).
Proof.
  intros t s Ht. unfold amo_store_bytes. cbn [amo_val].
  rewrite bv_add_unsigned.
  rewrite (le_word_v _ (Z_to_bv 64 t)) by (rewrite bytes_le_to_Z_8; reflexivity).
  rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
  unfold word_to_le_bytes.
  rewrite (u64_lit ((t + bv_unsigned s) mod 2 ^ 64)) by (pose proof (Z.mod_pos_bound (t + bv_unsigned s) (2 ^ 64)); lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. f_equal.
  rewrite !(Z.mod_small t) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_amoadd_w : forall regs pc mem rom w aq rl rd rs1 rs2 a t,
  fetch_word SEGS pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo AMO_ADD AW aq rl rd rs1 rs2, 4%Z) ->
  getr regs rs1 = Z_to_bv 64 a -> (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z -> (a mod 4 = 0)%Z ->
  cell32 mem a t -> (t < 2 ^ 31)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 4 = true ->
  RiscvSemantics.step SEGS (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 t)) (v_addi pc 4)
                  (wbytes mem (Z_to_bv 64 a) (word_to_le_bytes 4 (Z_to_bv 64 ((t + bv_unsigned (getr regs rs2)) mod 2 ^ 32)))) rom).
Proof.
  intros regs pc mem rom w aq rl rd rs1 rs2 a t HF HE HD Ha Ha0 Ha4 Hal [Hc Ht] Ht31 Hok.
  rewrite <- (mkstR_None regs pc mem rom).
  rewrite (stepR_amo SEGS regs pc mem rom None w AMO_ADD AW aq rl rd rs1 rs2 (word_to_le_bytes 4 (Z_to_bv 64 t)) HF HE HD).
  - cbn [amo_msize resv_inval_w]. rewrite load_result_w by lia. rewrite Ha, amo_add_w_bytes by lia. reflexivity.
  - rewrite Ha. unfold amo_bytes. rewrite u64_lit by lia. exact Hal.
  - rewrite Ha. exact Hc.
  - rewrite Ha. exact Hok.
Qed.

Lemma step_amoadd_d : forall regs pc mem rom w aq rl rd rs1 rs2 a t,
  fetch_word SEGS pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo AMO_ADD AD aq rl rd rs1 rs2, 4%Z) ->
  getr regs rs1 = Z_to_bv 64 a -> (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z -> (a mod 8 = 0)%Z ->
  cell64 mem a t -> store_ok SEGS mem (Z_to_bv 64 a) 8 = true ->
  RiscvSemantics.step SEGS (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 t)) (v_addi pc 4)
                  (wbytes mem (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 ((t + bv_unsigned (getr regs rs2)) mod 2 ^ 64)))) rom).
Proof.
  intros regs pc mem rom w aq rl rd rs1 rs2 a t HF HE HD Ha Ha0 Ha8 Hal [Hc Ht] Hok.
  rewrite <- (mkstR_None regs pc mem rom).
  rewrite (stepR_amo SEGS regs pc mem rom None w AMO_ADD AD aq rl rd rs1 rs2 (word_to_le_bytes 8 (Z_to_bv 64 t)) HF HE HD).
  - cbn [amo_msize resv_inval_w]. rewrite load_result_d by (cbn in Ht; lia). rewrite Ha, amo_add_d_bytes by (cbn in Ht; lia). reflexivity.
  - rewrite Ha. unfold amo_bytes. rewrite u64_lit by lia. exact Hal.
  - rewrite Ha. exact Hc.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)
Lemma steps_lr_bne_sc : forall regs pc mem rom w1 w2 w3 aq1 rl1 aq3 rl3 (rd rs rcmp rd3 rs2 : bv 5) (imm : bv 13) a t tgt,
  fetch_word SEGS pc = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Lr AW aq1 rl1 rd rs, 4%Z) ->
  fetch_word SEGS (v_addi pc 4) = Some w2 -> is_ecall w2 = false -> decode_any w2 = Some (Branch BC_NE rd rcmp imm, 4%Z) ->
  fetch_word SEGS (v_addi (v_addi pc 4) 4) = Some w3 -> is_ecall w3 = false -> decode_any w3 = Some (Sc AW aq3 rl3 rd3 rs rs2, 4%Z) ->
  rd <> 0 -> rd <> rs -> rd <> rcmp -> rd <> rs2 -> rd3 <> 0 ->
  getr regs rs = Z_to_bv 64 a -> (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z -> (a mod 4 = 0)%Z ->
  cell32 mem a t -> (t < 2 ^ 31)%Z -> getr regs rcmp = Z_to_bv 64 t ->
  store_ok SEGS mem (Z_to_bv 64 a) 4 = true ->
  msteps SEGS (mkst (regupd (regupd regs rd (Z_to_bv 64 t)) rd3 (Z_to_bv 64 0)) (v_addi (v_addi (v_addi pc 4) 4) 4)
                    (wbytes mem (Z_to_bv 64 a) (word_to_le_bytes 4 (getr regs rs2))) rom) tgt ->
  msteps SEGS (mkst regs pc mem rom) tgt.
Proof.
  intros regs pc mem rom w1 w2 w3 aq1 rl1 aq3 rl3 rd rs rcmp rd3 rs2 imm a t tgt
         F1 E1 D1 F2 E2 D2 F3 E3 D3 N0 N1 N2 N3 N4 Hrs Ha0 Ha4 Hal [Hc Ht] Ht31 Hcmp Hok REST.
  rewrite <- (mkstR_None regs pc mem rom).
  eapply mst_step; [reflexivity | |].
  { rewrite (stepR_lr SEGS regs pc mem rom None w1 AW aq1 rl1 rd rs (word_to_le_bytes 4 (Z_to_bv 64 t)) F1 E1 D1).
    - reflexivity.
    - rewrite Hrs. unfold amo_bytes. rewrite u64_lit by lia. exact Hal.
    - rewrite Hrs. exact Hc. }
  replace (bv_eqb rd 0) with false by (symmetry; apply bv_eqb_neq; exact N0). cbv iota.
  cbn [amo_msize]. rewrite load_result_w by lia.
  eapply mst_step; [reflexivity | |].
  { apply (stepR_branch_ft_gen SEGS _ _ mem rom _ w2 BC_NE rd rcmp imm F2 E2 D2).
    cbn [branch_taken]. rewrite getr_same by exact N0. rewrite getr_other by (intros E; exact (N2 (eq_sym E))). rewrite Hcmp.
    rewrite bv_eqb_refl. reflexivity. }
  eapply mst_step; [reflexivity | |].
  { rewrite (stepR_sc_ok SEGS _ _ mem rom w3 AW aq3 rl3 rd3 rs rs2 (getr regs rs) F3 E3 D3).
    - reflexivity.
    - rewrite getr_other by (intros E; exact (N1 (eq_sym E))). rewrite Hrs. unfold amo_bytes. rewrite u64_lit by lia. exact Hal.
    - rewrite getr_other by (intros E; exact (N1 (eq_sym E))). reflexivity.
    - rewrite getr_other by (intros E; exact (N1 (eq_sym E))). rewrite Hrs. exact Hok. }
  replace (bv_eqb rd3 0) with false by (symmetry; apply bv_eqb_neq; exact N4). cbv iota.
  cbn [amo_nbytes]. rewrite mkstR_None.
  rewrite (getr_other regs rd _ rs) by (intros E; exact (N1 (eq_sym E))).
  rewrite (getr_other regs rd _ rs2) by (intros E; exact (N3 (eq_sym E))). rewrite Hrs.
  exact REST.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_addiw_lit : forall a imm, (0 <= a < 2 ^ 64)%Z -> (- 2 ^ 31 <= a + imm < 2 ^ 31)%Z -> (0 <= a + imm)%Z ->
  v_addiw (Z_to_bv 64 a) imm = Z_to_bv 64 (a + imm).
Proof. intros a imm Ha Hs Hp. unfold v_addiw. rewrite u64_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

Lemma v_sltiu1_nz : forall z, (1 <= z < 2 ^ 64)%Z -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 0.
Proof.
  intros z Hz. unfold v_sltiu. rewrite u64_lit by lia. change (bv_wrap 64 1) with 1%Z.
  destruct (z <? 1)%Z eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
Qed.

Lemma v_sltiu1_z : v_sltiu (Z_to_bv 64 0) 1 = Z_to_bv 64 1.
Proof. reflexivity. Qed.

Lemma lxor_range64 : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> (0 <= Z.lxor a b < 2 ^ 64)%Z.
Proof.
  intros a b Ha Hb. assert (H0 : (0 <= Z.lxor a b)%Z) by (apply Z.lxor_nonneg; lia). split; [exact H0|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as HL.
  assert (Z.log2 a < 64)%Z by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
  assert (Z.log2 b < 64)%Z by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
  lia.
Qed.

Lemma v_xor_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
Proof. intros. unfold v_xor. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma lxor_nz : forall a b, a <> b -> Z.lxor a b <> 0%Z.
Proof. intros a b H E. apply H. apply Z.lxor_eq. exact E. Qed.

Lemma land_low_high : forall t k c, (0 <= t < 2 ^ k)%Z -> (0 <= k)%Z -> (0 <= c)%Z -> Z.land t (c * 2 ^ k) = 0%Z.
Proof.
  intros t k c Ht Hk Hc. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec i k).
  - rewrite Z.mul_pow2_bits_low by lia. apply Bool.andb_false_r.
  - replace (Z.testbit t i) with false; [reflexivity|]. symmetry. apply Z.testbit_false; [lia|].
    rewrite Z.div_small; [reflexivity|]. split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Ht)|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma lor_disjoint_add : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
  intros a b k Ha Hk Hb. rewrite <- Z.lxor_lor.
  - symmetry. apply Z.add_nocarry_lxor. rewrite Z.land_comm. apply land_low_high; lia.
  - rewrite Z.land_comm. apply land_low_high; lia.
Qed.

(* [comment removed for export] *)
Lemma skipn_Z_to_le_bytes : forall k n z, (k <= n)%nat ->
  skipn k (Z_to_le_bytes n z) = Z_to_le_bytes (n - k) (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction k as [|k IH]; intros n z Hk.
  - cbn [skipn]. rewrite Nat.sub_0_r, Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - destruct n as [|n]; [lia|]. cbn [Z_to_le_bytes skipn]. rewrite IH by lia.
    replace (S n - S k)%nat with (n - k)%nat by lia. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma rdn_hi32 : forall m a v, (0 <= a)%Z -> (a + 8 < 2 ^ 64)%Z -> (0 <= v < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) ->
  rdn SEGS m (Z_to_bv 64 (a + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (v / 2 ^ 32))).
Proof.
  intros m a v Ha Ha8 Hv H.
  pose proof (rdn_skipn SEGS m 8 (Z_to_bv 64 a) _ 4 H ltac:(lia)) as R.
  unfold at_ in R. rewrite u64_lit in R by lia.
  replace (Z.of_nat 4) with 4%Z in R by reflexivity. replace (8 - 4)%nat with 4%nat in R by reflexivity. rewrite R. f_equal. unfold word_to_le_bytes. rewrite skipn_Z_to_le_bytes by lia. cbn [Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ].
  rewrite !u64_lit; [| pose proof (Z.div_pos v (2 ^ 32)); pose proof (Z.div_lt_upper_bound v (2 ^ 32) (2 ^ 32)); lia | lia].
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma rdn_lo32 : forall m a v, (0 <= v < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) ->
  rdn SEGS m (Z_to_bv 64 a) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (v mod 2 ^ 32))).
Proof.
  intros m a v Hv H. rewrite (rdn_low_bytes SEGS m _ _ 4 ltac:(lia) H). f_equal.
  unfold word_to_le_bytes. rewrite (Z_to_le_bytes_mod 4 (bv_unsigned (Z_to_bv 64 v))).
  rewrite !u64_lit; [| pose proof (Z.mod_pos_bound v (2 ^ 32)); lia | lia].
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. reflexivity.
Qed.

Lemma v_andi_m16_small : forall z, (0 <= z < 16)%Z -> v_andi (Z_to_bv 64 z) (-16) = Z_to_bv 64 0.
Proof.
  intros z Hz. unfold v_andi. rewrite u64_lit by lia.
  change (bv_wrap 64 (-16)) with ((2 ^ 60 - 1) * 2 ^ 4)%Z. rewrite land_low_high by lia. reflexivity.
Qed.


(* [comment removed for export] *)
Definition hideP (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change T with (hideP T) in H end.
Ltac unhide H := unfold hideP in H.
Ltac hide_disjs := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (hideP (A \/ B)) in H end.

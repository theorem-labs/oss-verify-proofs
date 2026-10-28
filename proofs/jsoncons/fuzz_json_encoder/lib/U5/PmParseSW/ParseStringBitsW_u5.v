(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg SymExec AxSymExec3
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmRef_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParseSW Require Import UvZ.
Import ListNotations. Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac dlia := Z.div_mod_to_equations; lia.
Ltac dnia := Z.div_mod_to_equations; nia.

Module PSBT.
Import UVZ.
Abbreviation uv := PB.uv.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lor_disjoint : forall a c k, 0 <= a -> 0 <= k -> 0 <= c < 2 ^ k -> Z.lor (a * 2 ^ k) c = a * 2 ^ k + c.
Proof.
  intros a c k Ha Hk Hc.
  assert (HL : Z.land (a * 2 ^ k) c = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.testbit_0_l.
    destruct (Z_lt_dec n k) as [L|L].
    - rewrite Z.mul_pow2_bits_low by dlia. reflexivity.
    - destruct (Z.eq_dec c 0) as [->|Hc0]; [rewrite Z.testbit_0_l; apply Bool.andb_false_r|].
      assert (HL2 : Z.log2 c < k) by (apply Z.log2_lt_pow2; dlia).
      rewrite (Z.bits_above_log2 c n) by dlia. apply Bool.andb_false_r. }
  rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.
Lemma lor_disjoint' : forall c a k, 0 <= a -> 0 <= k -> 0 <= c < 2 ^ k -> Z.lor c (a * 2 ^ k) = a * 2 ^ k + c.
Proof. intros c a k Ha Hk Hc. rewrite Z.lor_comm. apply lor_disjoint; assumption. Qed.
Lemma land_ones' : forall a k, 0 <= k -> Z.land a (2 ^ k - 1) = a mod 2 ^ k.
Proof. intros a k Hk. rewrite <- (Z.land_ones a k Hk). unfold Z.ones. rewrite Z.shiftl_mul_pow2, Z.mul_1_l by dlia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma land_mod_r : forall x m n, 0 <= x < 2 ^ n -> 0 <= n -> Z.land x (m mod 2 ^ n) = Z.land x m.
Proof.
  intros x m n Hx Hn. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z_lt_dec i n) as [L|L]; [rewrite Z.mod_pow2_bits_low by dlia; reflexivity|].
  destruct (Z.eq_dec x 0) as [->|Hx0]; [rewrite Z.testbit_0_l; reflexivity|].
  rewrite (Z.bits_above_log2 x i); [reflexivity | dlia | apply Z.log2_lt_pow2 in L || pose proof (proj1 (Z.log2_lt_pow2 x n ltac:(dlia)) ltac:(dlia)); dlia].
Qed.
(* [comment removed for export] *)
Lemma land_notmask : forall x m, 0 <= x < 2 ^ 64 -> Z.land x ((- m - 1) mod 2 ^ 64) = x - Z.land x m.
Proof. intros x m Hx. rewrite (land_mod_r x (- m - 1) 64 Hx ltac:(dlia)). replace (- m - 1) with (Z.lnot m) by (unfold Z.lnot; dlia). symmetry. apply Z.sub_land_same_l. Qed.
Lemma land_notmask' : forall x nm m, 0 <= x < 2 ^ 64 -> nm = - m - 1 -> Z.land x (nm mod 2 ^ 64) = x - Z.land x m.
Proof. intros x nm m Hx ->. apply land_notmask. exact Hx. Qed.
Lemma land_nonneg_l : forall a b, 0 <= a -> 0 <= Z.land a b.
Proof. intros a b Ha. apply (proj2 (Z.land_nonneg a b)). left. exact Ha. Qed.
Lemma land_le_l : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros a b Ha Hb. pose proof (Z.sub_land_same_l a b) as E. pose proof (land_nonneg_l a (Z.lnot b) Ha). dlia.
Qed.
Lemma lor_bound : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb. split; [apply Z.lor_nonneg; dlia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E0|NE]; [rewrite E0; dlia|].
  assert (Hn : 0 <= n) by (destruct (Z_lt_dec n 0); [rewrite Z.pow_neg_r in Ha by dlia; dlia | dlia]).
  pose proof (proj2 (Z.lor_nonneg a b) (conj (proj1 Ha) (proj1 Hb))) as Hp.
  apply Z.log2_lt_pow2; [dlia|]. rewrite Z.log2_lor by dlia.
  destruct (Z.eq_dec a 0) as [->|Na]; destruct (Z.eq_dec b 0) as [->|Nb].
  - exfalso. apply NE. reflexivity.
  - rewrite Z.max_r by (cbn; apply Z.log2_nonneg). apply Z.log2_lt_pow2; dlia.
  - rewrite Z.max_l by (cbn; apply Z.log2_nonneg). apply Z.log2_lt_pow2; dlia.
  - apply Z.max_lub_lt; apply Z.log2_lt_pow2; dlia.
Qed.
Lemma lor_as_sub_add : forall y m, y - Z.land y m + m = Z.lor y m.
Proof. intros y m. rewrite Z.sub_land_same_l, <- Z.sub_lor_l_same_r. dlia. Qed.
(* [comment removed for export] *)
Definition allr (lo n : Z) (f : Z -> bool) : bool := forallb f (map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat n))).
Lemma allr_sound : forall lo n f, allr lo n f = true -> forall z, lo <= z < lo + n -> f z = true.
Proof.
  intros lo n f H z Hz. unfold allr in H. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat (z - lo)). split; [dlia|]. apply in_seq. dlia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section UvSteps.
Variable E : env.
Lemma uv_range : forall e, 0 <= uv E e < 2 ^ 64. Proof. intros e. unfold PB.uv. apply u64_range. Qed.
Lemma uv_lit : forall z, uv E (ELit z) = z mod 2 ^ 64. Proof. intros z. unfold PB.uv. cbn [edenot]. apply lit64_u. Qed.
Lemma uv_add : forall a b, uv E (EAlu ALU_ADD a b) = (uv E a + uv E b) mod 2 ^ 64.
Proof. intros a b. unfold PB.uv. cbn [edenot]. apply (alu64_sound ALU_ADD). reflexivity. Qed.
Lemma uv_sub : forall a b, uv E (EAlu ALU_SUB a b) = (uv E a - uv E b) mod 2 ^ 64.
Proof. intros a b. unfold PB.uv. cbn [edenot]. apply (alu64_sound ALU_SUB). reflexivity. Qed.
Lemma uv_and : forall a b, uv E (EAlu ALU_AND a b) = Z.land (uv E a) (uv E b).
Proof. intros a b. unfold PB.uv. cbn [edenot]. apply (alu64_sound ALU_AND). reflexivity. Qed.
Lemma uv_or : forall a b, uv E (EAlu ALU_OR a b) = Z.lor (uv E a) (uv E b).
Proof. intros a b. unfold PB.uv. cbn [edenot]. apply (alu64_sound ALU_OR). reflexivity. Qed.
Lemma uv_sltu : forall a b, uv E (EAlu ALU_SLTU a b) = (if uv E a <? uv E b then 1 else 0).
Proof. intros a b. unfold PB.uv. cbn [edenot]. apply (alu64_sound ALU_SLTU). reflexivity. Qed.
Lemma uv_mul : forall a b, uv E (EMd M_MUL a b) = (uv E a * uv E b) mod 2 ^ 64.
Proof. intros a b. unfold PB.uv. cbn [edenot]. unfold mul_div. rewrite bv_mul_unsigned. apply wrap64. Qed.
Lemma uv_srl_lit : forall a k, 0 <= k < 64 -> uv E (EAlu ALU_SRL a (ELit k)) = uv E a / 2 ^ k.
Proof.
  intros a k Hk. unfold PB.uv. cbn [edenot]. rewrite (alu64_sound ALU_SRL _ _ (Z.shiftr (bv_unsigned (edenot E a)) (Z.land (bv_unsigned (Z_to_bv 64 k)) 63)) eq_refl).
  rewrite lit64_u. unfold w64. rewrite (Z.mod_small k) by dlia. change 63 with (2 ^ 6 - 1). rewrite land_ones', (Z.mod_small k) by dlia. apply Z.shiftr_div_pow2. dlia.
Qed.
Lemma uv_ext04 : forall a, uv E (EExt true 0 4 a) = sx32 (uv E a mod 2 ^ 32).
Proof.
  intros a. unfold PB.uv. cbn [edenot]. unfold ext_val. rewrite lit64_u. unfold ext_Z.
  change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change (8 * N.of_nat 4)%N with 32%N. rewrite Z.div_1_r.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E a)) (2 ^ 32) ltac:(dlia)) as Hr. rewrite (swrap32 _ Hr).
  unfold w64, sx32. rewrite (Z.mod_small (_ mod 2 ^ 32) (2 ^ 32)) by dlia.
  destruct (Z.ltb_spec (bv_unsigned (edenot E a) mod 2 ^ 32) (2 ^ 31)); [rewrite Z.mod_small by dlia; reflexivity|].
  rewrite <- (Z.mod_add _ 1) by dlia. rewrite Z.mod_small by dlia. dlia.
Qed.
Lemma uv_addw : forall a b, uv E (EAluw ALU_ADD a b) = sx32 (uv E a mod 2 ^ 32 + uv E b mod 2 ^ 32).
Proof. intros a b. unfold PB.uv. cbn [edenot]. apply (aluw_sound ALU_ADD). reflexivity. Qed.
Lemma uv_sllw_lit : forall a k, 0 <= k < 32 -> uv E (EAluw ALU_SLL a (ELit k)) = sx32 ((uv E a mod 2 ^ 32) * 2 ^ k).
Proof.
  intros a k Hk. unfold PB.uv. cbn [edenot].
  rewrite (aluw_sound ALU_SLL _ _ (sx32 (Z.shiftl (bv_unsigned (edenot E a) mod 2 ^ 32) (Z.land (bv_unsigned (Z_to_bv 64 k) mod 2 ^ 32) 31))) eq_refl).
  rewrite lit64_u. unfold w64. rewrite (Z.mod_small k (2 ^ 64)), (Z.mod_small k (2 ^ 32)) by dlia. change 31 with (2 ^ 5 - 1). rewrite land_ones', (Z.mod_small k) by dlia.
  rewrite Z.shiftl_mul_pow2 by dlia. reflexivity.
Qed.
Lemma uv_srlw_lit : forall a k, 0 <= k < 32 -> uv E (EAluw ALU_SRL a (ELit k)) = sx32 ((uv E a mod 2 ^ 32) / 2 ^ k).
Proof.
  intros a k Hk. unfold PB.uv. cbn [edenot].
  rewrite (aluw_sound ALU_SRL _ _ (sx32 (Z.shiftr (bv_unsigned (edenot E a) mod 2 ^ 32) (Z.land (bv_unsigned (Z_to_bv 64 k) mod 2 ^ 32) 31))) eq_refl).
  rewrite lit64_u. unfold w64. rewrite (Z.mod_small k (2 ^ 64)), (Z.mod_small k (2 ^ 32)) by dlia. change 31 with (2 ^ 5 - 1). rewrite land_ones', (Z.mod_small k) by dlia.
  rewrite Z.shiftr_div_pow2 by dlia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma sx32_mod : forall z, sx32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. unfold sx32. pose proof (Z.mod_pos_bound z (2 ^ 32) ltac:(dlia)). destruct (Z.ltb_spec (z mod 2 ^ 32) (2 ^ 31)); [apply Z.mod_mod; dlia|].
  rewrite <- (Z.mod_add _ (- 2 ^ 32 + 1)) by dlia. rewrite (Z.mod_small); [|dlia]. dlia.
Qed.
Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 z = z.
Proof. intros z Hz. unfold sx32. rewrite Z.mod_small by dlia. destruct (Z.ltb_spec z (2 ^ 31)); dlia. Qed.
Lemma sx32_range : forall z, 0 <= sx32 z < 2 ^ 64.
Proof. intros z. unfold sx32. pose proof (Z.mod_pos_bound z (2 ^ 32) ltac:(dlia)). destruct (Z.ltb_spec (z mod 2 ^ 32) (2 ^ 31)); dlia. Qed.
Lemma sx32_idem : forall z, sx32 (sx32 z) = sx32 z.
Proof. intros z. unfold sx32 at 1. rewrite sx32_mod. reflexivity. Qed.
Lemma sx32_big : forall z, 2 ^ 31 <= z mod 2 ^ 32 -> sx32 z = z mod 2 ^ 32 + 2 ^ 64 - 2 ^ 32.
Proof. intros z Hz. unfold sx32. destruct (Z.ltb_spec (z mod 2 ^ 32) (2 ^ 31)); dlia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hexv (cp d : Z) : Z := (cp * 16 + d) mod 2 ^ 32.
Lemma mod32_of_64 : forall z, (z mod 2 ^ 64) mod 2 ^ 32 = z mod 2 ^ 32.
Proof. intros z. apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity. Qed.
Lemma sx32_eqm : forall y z, y mod 2 ^ 32 = z mod 2 ^ 32 -> sx32 y = sx32 z.
Proof. intros y z H. unfold sx32. rewrite H. reflexivity. Qed.
(* [comment removed for export] *)
Lemma uv_sll4 : forall ecp cp, uv E ecp mod 2 ^ 32 = cp -> uv E (EAluw ALU_SLL (EExt true 0 4 ecp) (ELit 4)) = sx32 (cp * 16).
Proof.
  intros ecp cp Hcp. rewrite uv_sllw_lit by dlia. rewrite uv_ext04, sx32_mod, Z.mod_mod, Hcp by dlia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma atom_addw : forall ecp eb cp b k, uv E ecp mod 2 ^ 32 = cp -> uv E eb = b ->
  uv E (EAluw ALU_ADD (EAlu ALU_ADD eb (EAluw ALU_SLL (EExt true 0 4 ecp) (ELit 4))) (ELit (- k))) = sx32 (hexv cp (b - k)).
Proof.
  intros ecp eb cp b k Hcp Hb. rewrite uv_addw, uv_add, (uv_sll4 ecp cp Hcp), Hb, uv_lit, !mod32_of_64. unfold hexv. apply sx32_eqm.
  rewrite Z.mod_mod, <- Z.add_mod by dlia. replace (b + sx32 (cp * 16) + - k) with (sx32 (cp * 16) + (b - k)) by dlia.
  rewrite Z.add_mod, sx32_mod, <- Z.add_mod by dlia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma atom_or : forall ecp eb cp b, uv E ecp mod 2 ^ 32 = cp -> uv E eb = b -> 0 <= cp -> 48 <= b <= 57 ->
  uv E (EAlu ALU_OR (EAlu ALU_ADD eb (ELit (-48))) (EAluw ALU_SLL (EExt true 0 4 ecp) (ELit 4))) = sx32 (hexv cp (b - 48)).
Proof.
  intros ecp eb cp b Hcp Hb Hcp0 Hbr. rewrite uv_or, uv_add, Hb, uv_lit, (uv_sll4 ecp cp Hcp).
  assert (E1 : (b + (-48) mod 2 ^ 64) mod 2 ^ 64 = b + -48) by (rewrite Z.add_mod_idemp_r by dlia; apply Z.mod_small; dlia). rewrite E1.
  (* [comment removed for export] *)
  assert (HM : (cp * 16) mod 2 ^ 32 = 16 * (cp mod 2 ^ 28)) by (rewrite (Z.mul_comm cp 16); change (2 ^ 32) with (16 * 2 ^ 28); apply Z.mul_mod_distr_l; dlia).
  pose proof (Z.mod_pos_bound cp (2 ^ 28) ltac:(dlia)) as HMr. set (M := cp mod 2 ^ 28) in *.
  assert (H16 : exists q, 0 <= q /\ sx32 (cp * 16) = q * 2 ^ 4).
  { unfold sx32. rewrite HM. destruct (Z.ltb_spec (16 * M) (2 ^ 31)).
    - exists M. split; [dlia | change (2 ^ 4) with 16; dlia].
    - exists (M + 2 ^ 60 - 2 ^ 28). split; [dlia | change (2 ^ 4) with 16; dlia]. }
  destruct H16 as (q & Hq & Hq16). rewrite Hq16, (lor_disjoint' (b + -48) q 4 Hq ltac:(dlia) ltac:(change (2 ^ 4) with 16; dlia)), <- Hq16.
  unfold hexv, sx32. rewrite Z.mod_mod, Z.add_mod, HM, (Z.mod_small (b - 48)), (Z.mod_small (16 * M + (b - 48))) by dlia.
  destruct (Z.ltb_spec (16 * M) (2 ^ 31)); destruct (Z.ltb_spec (16 * M + (b - 48)) (2 ^ 31)); dlia.
Qed.
(* [comment removed for export] *)
Lemma atom_lin : forall eb b k, uv E eb = b -> 0 <= k <= b -> b < 256 -> uv E (EAlu ALU_ADD eb (ELit (- k))) = b - k.
Proof. intros eb b k Hb Hk Hbr. rewrite uv_add, Hb, uv_lit, Z.add_mod_idemp_r by dlia. apply Z.mod_small. dlia. Qed.
Lemma hexv_0 : forall d, 0 <= d < 16 -> hexv 0 d = d.
Proof. intros d Hd. unfold hexv. apply Z.mod_small. dlia. Qed.
(* [comment removed for export] *)
Lemma uv_ext04_sx : forall a x, uv E a = sx32 x -> uv E (EExt true 0 4 a) = sx32 x.
Proof. intros a x H. rewrite uv_ext04, H, sx32_mod. unfold sx32. rewrite Z.mod_mod by dlia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod64_lt1 : forall d, - 2 ^ 63 < d < 2 ^ 63 -> (d mod 2 ^ 64 <? 1) = (d =? 0).
Proof.
  intros d Hd. destruct (Z.eqb_spec d 0) as [->|Hne]; [reflexivity|]. apply Z.ltb_ge.
  destruct (Z_lt_dec d 0); [rewrite <- (Z.mod_add _ 1), Z.mod_small by dlia; dlia | rewrite Z.mod_small by dlia; dlia].
Qed.
Section Shapes.
Variable H : expr.
Variable x : Z.
Hypothesis UH : uv E H = sx32 x.
Hypothesis Hx : 0 <= x < 2 ^ 32.
Lemma H32 : uv E H mod 2 ^ 32 = x. Proof. rewrite UH, sx32_mod. apply Z.mod_small. exact Hx. Qed.
(* [comment removed for export] *)
Lemma f_hs : uv E (EAlu ALU_SLTU (EAlu ALU_SUB (EAluw ALU_SRL H (ELit 10)) (ELit 54)) (ELit 1)) = (if x / 1024 =? 54 then 1 else 0).
Proof.
  rewrite uv_sltu, uv_sub, uv_srlw_lit, H32, !uv_lit by dlia. change (2 ^ 10) with 1024. rewrite (sx32_small (x / 1024)) by dlia.
  rewrite (Z.mod_small 54), (Z.mod_small 1) by dlia. rewrite mod64_lt1 by dlia. destruct (Z.eqb_spec (x / 1024 - 54) 0); destruct (Z.eqb_spec (x / 1024) 54); try dlia; reflexivity.
Qed.
(* [comment removed for export] *)
Lemma f_lt128 : uv E (EAlu ALU_SLTU H (ELit 128)) = (if x <? 128 then 1 else 0).
Proof.
  rewrite uv_sltu, UH, uv_lit, (Z.mod_small 128) by dlia. unfold sx32. rewrite (Z.mod_small x) by dlia.
  destruct (Z.ltb_spec x (2 ^ 31)); destruct (Z.ltb_spec x 128) as [L|L].
  - reflexivity.
  - reflexivity.
  - exfalso. dlia.
  - rewrite (proj2 (Z.ltb_ge _ 128)) by dlia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma f_surr : uv E (EAlu ALU_SLTU (EAlu ALU_SUB (EMd M_MUL (ELit 2048) (EAlu ALU_SRL H (ELit 11))) (ELit 55296)) (ELit 1)) =
  (if (55296 <=? x) && (x <? 57344) then 1 else 0).
Proof.
  rewrite uv_sltu, uv_sub, uv_mul, uv_srl_lit, UH, !uv_lit, (Z.mod_small 2048), (Z.mod_small 55296), (Z.mod_small 1) by dlia. change (2 ^ 11) with 2048.
  unfold sx32. rewrite (Z.mod_small x) by dlia.
  destruct (Z.ltb_spec x (2 ^ 31)) as [L|L].
  - rewrite (Z.mod_small (2048 * (x / 2048))) by dlia. rewrite mod64_lt1 by dlia.
    destruct (Z.eqb_spec (2048 * (x / 2048) - 55296) 0); destruct (Z.leb_spec 55296 x); destruct (Z.ltb_spec x 57344); cbn [andb]; try reflexivity; dlia.
  - replace ((x + 2 ^ 64 - 2 ^ 32) / 2048) with (x / 2048 + (2 ^ 53 - 2 ^ 21)) by dlia.
    replace (2048 * (x / 2048 + (2 ^ 53 - 2 ^ 21))) with (2048 * (x / 2048) + (2 ^ 64 - 2 ^ 32)) by dlia. rewrite (Z.mod_small (2048 * (x / 2048) + (2 ^ 64 - 2 ^ 32))) by dlia.
    rewrite (Z.mod_small) by dlia. destruct (Z.ltb_spec (2048 * (x / 2048) + (2 ^ 64 - 2 ^ 32) - 55296) 1); [exfalso; dlia|].
    destruct (Z.leb_spec 55296 x); destruct (Z.ltb_spec x 57344); cbn [andb]; try reflexivity; dlia.
Qed.
(* [comment removed for export] *)
Lemma f_srlw0 : forall k, 0 < k < 32 -> uv E (EAlu ALU_SLTU (EAlu ALU_SUB (EAluw ALU_SRL H (ELit k)) (ELit 0)) (ELit 1)) = (if x <? 2 ^ k then 1 else 0).
Proof.
  intros k Hk. rewrite uv_sltu, uv_sub, uv_srlw_lit, H32, !uv_lit, (Z.mod_small 0), (Z.mod_small 1) by dlia.
  assert (Hq : 0 <= x / 2 ^ k < 2 ^ 31).
  { split; [apply Z.div_pos; dlia|]. apply Z.div_lt_upper_bound; [dlia|]. assert (2 <= 2 ^ k) by (apply Z.pow_le_mono_r with (b := 1) in Hk || idtac; replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; dlia). dnia. }
  rewrite (sx32_small (x / 2 ^ k)) by dlia. rewrite Z.sub_0_r, mod64_lt1 by dlia.
  destruct (Z.eqb_spec (x / 2 ^ k) 0); destruct (Z.ltb_spec x (2 ^ k)); try reflexivity; exfalso.
  - pose proof (Z.div_str_pos x (2 ^ k)). assert (0 < 2 ^ k) by dlia. pose proof (Z.div_le_lower_bound x (2 ^ k) 1 ltac:(dlia) ltac:(dlia)). dlia.
  - rewrite Z.div_small in n by dlia. exact (n eq_refl).
Qed.
(* [comment removed for export] *)
Lemma f_gt : uv E (EAlu ALU_SLTU (ELit 16) (EAluw ALU_SRL H (ELit 16))) = (if 1114111 <? x then 1 else 0).
Proof.
  rewrite uv_sltu, uv_srlw_lit, H32, uv_lit, (Z.mod_small 16) by dlia. change (2 ^ 16) with 65536. rewrite (sx32_small (x / 65536)) by dlia.
  destruct (Z.ltb_spec 16 (x / 65536)); destruct (Z.ltb_spec 1114111 x); try reflexivity; exfalso; dlia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_byte : forall z m, 0 <= m < 256 -> Z.land z m = Z.land (z mod 256) m.
Proof. intros z m Hm. rewrite (Z.land_comm z m), (Z.land_comm (z mod 256) m). symmetry. change 256 with (2 ^ 8). apply land_mod_r; dlia. Qed.
(* [comment removed for export] *)
Lemma v_and255 : uv E (EAlu ALU_AND H (ELit 255)) = x mod 256.
Proof.
  rewrite uv_and, UH, uv_lit, (Z.mod_small 255) by dlia. change 255 with (2 ^ 8 - 1). rewrite land_ones' by dlia. change (2 ^ 8) with 256.
  unfold sx32. rewrite (Z.mod_small x) by dlia. destruct (Z.ltb_spec x (2 ^ 31)); [reflexivity|].
  rewrite <- (Z.mod_add _ (- (2 ^ 56 - 2 ^ 24))) by dlia. f_equal. dlia.
Qed.
(* [comment removed for export] *)
Lemma v_cont0 : uv E (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_AND H (ELit 63)) (ELit (-128))) (ELit 255)) = 128 + x mod 64.
Proof.
  rewrite uv_and, uv_add, uv_and, UH, !uv_lit, (Z.mod_small 255) by dlia. change 63 with (2 ^ 6 - 1). rewrite (Z.mod_small (2 ^ 6 - 1)), land_ones' by dlia.
  change 255 with (2 ^ 8 - 1). rewrite land_ones' by dlia. change (2 ^ 8) with 256. change (2 ^ 6) with 64.
  assert (E6 : sx32 x mod 64 = x mod 64).
  { unfold sx32. rewrite (Z.mod_small x) by dlia. destruct (Z.ltb_spec x (2 ^ 31)); [reflexivity|]. rewrite <- (Z.mod_add _ (- (2 ^ 58 - 2 ^ 26))) by dlia. f_equal. dlia. }
  rewrite E6. dlia.
Qed.
(* [comment removed for export] *)
Lemma sx32_div_mod : forall k j, 0 <= k -> 0 <= j -> k + j <= 32 -> (sx32 x / 2 ^ k) mod 2 ^ j = (x / 2 ^ k) mod 2 ^ j.
Proof.
  intros k j Hk Hj Hkj. unfold sx32. rewrite (Z.mod_small x) by dlia. destruct (Z.ltb_spec x (2 ^ 31)); [reflexivity|].
  assert (Hp : 2 ^ 32 = 2 ^ k * 2 ^ (32 - k)) by (rewrite <- Z.pow_add_r by dlia; f_equal; dlia).
  assert (Hp2 : 2 ^ 64 = 2 ^ k * (2 ^ (32 - k) * 2 ^ 32)) by (rewrite Z.mul_assoc, <- Hp, <- Z.pow_add_r by dlia; f_equal; dlia).
  assert (Hq : 2 ^ (32 - k) = 2 ^ j * 2 ^ (32 - k - j)) by (rewrite <- Z.pow_add_r by dlia; f_equal; dlia).
  replace (x + 2 ^ 64 - 2 ^ 32) with (x + (2 ^ (32 - k) * 2 ^ 32 - 2 ^ (32 - k)) * 2 ^ k) by dlia.
  rewrite Z.div_add by dlia. rewrite Hq. replace (x / 2 ^ k + (2 ^ j * 2 ^ (32 - k - j) * 2 ^ 32 - 2 ^ j * 2 ^ (32 - k - j))) with
    (x / 2 ^ k + (2 ^ (32 - k - j) * 2 ^ 32 - 2 ^ (32 - k - j)) * 2 ^ j) by dlia. apply Z.mod_add. dlia.
Qed.
Lemma v_masked : forall k m j, 0 <= k -> 1 <= j <= 8 -> k + j <= 32 -> m = 256 - 2 ^ j ->
  uv E (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_AND (EAlu ALU_SRL H (ELit k)) (ELit (- m - 1))) (ELit m)) (ELit 255)) = m + (x / 2 ^ k) mod 2 ^ j.
Proof.
  intros k m j Hk Hj Hkj Hm. assert (Hk64 : k < 64) by dlia.
  assert (HJ : 2 <= 2 ^ j <= 256) by (split; [change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; dlia | change 256 with (2 ^ 8); apply Z.pow_le_mono_r; dlia]).
  assert (HK : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; dlia).
  rewrite uv_and, uv_add, uv_and, uv_srl_lit, UH, !uv_lit, (Z.mod_small m), (Z.mod_small 255) by dlia.
  set (y := sx32 x / 2 ^ k). pose proof (sx32_range x) as Hsx.
  assert (Hy : 0 <= y < 2 ^ 64) by (unfold y; split; [apply Z.div_pos; dlia | apply Z.div_lt_upper_bound; [dlia | dnia]]).
  rewrite (land_notmask y m Hy). pose proof (lor_bound y m 64 Hy ltac:(dlia)) as Hlor. rewrite (Z.mod_small (y - Z.land y m + m)) by (rewrite lor_as_sub_add; exact Hlor). change 255 with (2 ^ 8 - 1). rewrite land_ones' by dlia. change (2 ^ 8) with 256.
  rewrite <- (sx32_div_mod k j) by dlia. fold y.
  (* [comment removed for export] *)
  rewrite (land_byte y m) by dlia.
  assert (ID : forall w, 0 <= w < 256 -> (w - Z.land w m + m) mod 256 = m + w mod 2 ^ j).
  { intros w Hw. subst m.
    assert (A : allr 0 256 (fun w => forallb (fun j => ((w - Z.land w (256 - 2 ^ j) + (256 - 2 ^ j)) mod 256 =? (256 - 2 ^ j) + w mod 2 ^ j)) [1; 2; 3; 4; 5; 6; 7; 8]) = true) by (vm_compute; reflexivity).
    pose proof (allr_sound 0 256 _ A w Hw) as B. cbv beta in B. rewrite forallb_forall in B.
    assert (Hin : In j [1; 2; 3; 4; 5; 6; 7; 8]) by (cbn; dlia). apply Z.eqb_eq. exact (B j Hin). }
  transitivity (((y mod 256) - Z.land (y mod 256) m + m) mod 256); [dlia|].
  rewrite (ID (y mod 256)) by (apply Z.mod_pos_bound; dlia). f_equal. apply Z.mod_mod_divide. exists (2 ^ (8 - j)). rewrite <- Z.pow_add_r by dlia. replace (8 - j + j) with 8 by dlia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma v_cont : forall k, 0 <= k <= 26 ->
  uv E (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_AND (EAlu ALU_SRL H (ELit k)) (ELit (-129))) (ELit 128)) (ELit 191)) = 128 + (x / 2 ^ k) mod 64.
Proof.
  intros k Hk. assert (HK : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; dlia).
  rewrite uv_and, uv_add, uv_and, uv_srl_lit, UH, !uv_lit, (Z.mod_small 128), (Z.mod_small 191) by dlia.
  set (y := sx32 x / 2 ^ k). pose proof (sx32_range x) as Hsx.
  assert (Hy : 0 <= y < 2 ^ 64) by (unfold y; split; [apply Z.div_pos; dlia | apply Z.div_lt_upper_bound; [dlia | dnia]]).
  rewrite (land_notmask' y _ 128 Hy) by reflexivity. pose proof (lor_bound y 128 64 Hy ltac:(dlia)) as Hlor.
  rewrite (Z.mod_small (y - Z.land y 128 + 128)) by (rewrite lor_as_sub_add; exact Hlor).
  change 64 with (2 ^ 6). rewrite <- (sx32_div_mod k 6) by dlia. fold y. change (2 ^ 6) with 64.
  rewrite (land_byte (y - Z.land y 128 + 128) 191), (land_byte y 128) by dlia.
  assert (ID : forall w, 0 <= w < 256 -> Z.land ((w - Z.land w 128 + 128) mod 256) 191 = 128 + w mod 64).
  { intros w Hw. assert (A : allr 0 256 (fun w => Z.land ((w - Z.land w 128 + 128) mod 256) 191 =? 128 + w mod 64) = true) by (vm_compute; reflexivity).
    apply Z.eqb_eq. exact (allr_sound 0 256 _ A w Hw). }
  replace ((y - Z.land (y mod 256) 128 + 128) mod 256) with (((y mod 256) - Z.land (y mod 256) 128 + 128) mod 256) by dlia.
  rewrite (ID (y mod 256)) by (apply Z.mod_pos_bound; dlia). f_equal. apply Z.mod_mod_divide. exists 4. reflexivity.
Qed.
End Shapes.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma atom_t1 : forall ecp cp, uv E ecp mod 2 ^ 32 = cp ->
  uv E (EAlu ALU_SRL (EMd M_MUL (ELit 18014398509481984) (EExt true 0 4 ecp)) (ELit 44)) = (cp mod 1024) * 1024.
Proof.
  intros ecp cp Hcp. rewrite uv_srl_lit, uv_mul, uv_lit, uv_ext04, Hcp by dlia. change (18014398509481984 mod 2 ^ 64) with (2 ^ 54).
  change (2 ^ 64) with (2 ^ 54 * 2 ^ 10). rewrite Z.mul_mod_distr_l by dlia.
  replace (sx32 cp mod 2 ^ 10) with (cp mod 1024).
  2:{ change (2 ^ 10) with 1024. pose proof (sx32_mod cp) as M. rewrite <- (Z.mod_mod_divide (sx32 cp) (2 ^ 32) 1024) by (exists (2 ^ 22); reflexivity). rewrite M.
      symmetry. apply Z.mod_mod_divide. exists (2 ^ 22). reflexivity. }
  change (2 ^ 54) with (2 ^ 44 * 1024). rewrite <- Z.mul_assoc, (Z.mul_comm (2 ^ 44)), Z.div_mul by dlia. dlia.
Qed.
Lemma atom_pair : forall et ea cp x2, uv E et = (cp mod 1024) * 1024 -> uv E ea = sx32 x2 -> 0 <= x2 < 2 ^ 32 ->
  uv E (EAlu ALU_ADD (EAlu ALU_OR et (EAlu ALU_AND ea (ELit 1023))) (ELit 65536)) = PMR.pair_cp cp x2.
Proof.
  intros et ea cp x2 Ht Ha Hx2. rewrite uv_add, uv_or, uv_and, Ht, Ha, !uv_lit, (Z.mod_small 1023), (Z.mod_small 65536) by dlia.
  change 1023 with (2 ^ 10 - 1). rewrite land_ones' by dlia. pose proof (Z.mod_pos_bound cp 1024 ltac:(dlia)) as H1. pose proof (Z.mod_pos_bound (sx32 x2) (2 ^ 10) ltac:(dlia)) as H2.
  change 1024 with (2 ^ 10). rewrite lor_disjoint by dlia.
  replace (sx32 x2 mod 2 ^ 10) with (x2 mod 2 ^ 10).
  2:{ pose proof (sx32_mod x2) as M. rewrite <- (Z.mod_mod_divide (sx32 x2) (2 ^ 32) (2 ^ 10)) by (exists (2 ^ 22); reflexivity). rewrite M, (Z.mod_small x2 (2 ^ 32)) by dlia. reflexivity. }
  unfold PMR.pair_cp. change 1023 with (2 ^ 10 - 1). rewrite !land_ones', Z.shiftl_mul_pow2 by dlia. pose proof (Z.mod_pos_bound x2 (2 ^ 10) ltac:(dlia)).
  rewrite Z.mod_small; [dlia|]. change (2 ^ 10) with 1024 in *. dlia.
Qed.
(* [comment removed for export] *)
Lemma pair_sx32 : forall cp x2, sx32 (PMR.pair_cp cp x2) = PMR.pair_cp cp x2 /\ 0 <= PMR.pair_cp cp x2 < 2 ^ 21.
Proof.
  intros cp x2. unfold PMR.pair_cp. change 1023 with (2 ^ 10 - 1). rewrite !land_ones', Z.shiftl_mul_pow2 by dlia.
  pose proof (Z.mod_pos_bound cp (2 ^ 10) ltac:(dlia)). pose proof (Z.mod_pos_bound x2 (2 ^ 10) ltac:(dlia)).
  split; [apply sx32_small; dlia | dlia].
Qed.
Lemma uv_ext04_pair : forall ep cp x2, uv E ep = PMR.pair_cp cp x2 -> uv E (EExt true 0 4 ep) = sx32 (PMR.pair_cp cp x2).
Proof. intros ep cp x2 H. rewrite uv_ext04, H. destruct (pair_sx32 cp x2) as [S R]. rewrite Z.mod_small by dlia. reflexivity. Qed.
End UvSteps.
End PSBT.

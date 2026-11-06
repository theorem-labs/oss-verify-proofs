(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_grows : forall segs M M' n (a : word) bs,
  mem_grows M M' ->
  rdn segs M a n = Some bs ->
  exists bs', rdn segs M' a n = Some bs' /\ length bs' = n.
Proof.
  intros segs M M' n; induction n as [|n IH]; intros a bs HG H.
  - exists []. split; reflexivity.
  - cbn [rdn] in H |- *.
    destruct (match M a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Hb; [|discriminate].
    destruct (rdn segs M (a + 1) n) as [rest|] eqn:Hrest; [|discriminate].
    destruct (IH (a + 1)%bv rest HG Hrest) as (bs' & H' & L'). rewrite H'.
    destruct (M' a) as [b'|] eqn:HM'.
    + eexists. split; [reflexivity | cbn; rewrite L'; reflexivity].
    + destruct (M a) as [b0|] eqn:HM.
      * exfalso. apply (HG a); [rewrite HM; discriminate | exact HM'].
      * rewrite Hb. eexists. split; [reflexivity | cbn; rewrite L'; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma rdn_sub_Z : forall segs M (a : Z) (N : nat) bs (o : Z) (k : nat),
  0 <= a < 2 ^ 64 -> a + Z.of_nat N <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 a) N = Some bs ->
  0 <= o -> o + Z.of_nat k <= Z.of_nat N ->
  exists bs', rdn segs M (Z_to_bv 64 (a + o)) k = Some bs' /\ length bs' = k.
Proof.
  intros segs M a N bs o k Ha HaN H Ho Hok.
  pose proof (rdn_sub segs M N (Z_to_bv 64 a) bs (Z.to_nat o) k H ltac:(lia)) as HS.
  unfold at_ in HS. rewrite u_Z2bv in HS by lia. rewrite Z2Nat.id in HS by lia.
  eexists. split; [exact HS|]. unfold sub. rewrite length_firstn, length_skipn.
  pose proof (rdn_length _ _ _ _ _ H). lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_sub_grows : forall segs M M' (a : Z) (N : nat) bs (o : Z) (k : nat),
  0 <= a < 2 ^ 64 -> a + Z.of_nat N <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 a) N = Some bs -> mem_grows M M' ->
  0 <= o -> o + Z.of_nat k <= Z.of_nat N ->
  exists bs', rdn segs M' (Z_to_bv 64 (a + o)) k = Some bs' /\ length bs' = k.
Proof.
  intros segs M M' a N bs o k Ha HaN H HG Ho Hok.
  destruct (rdn_sub_Z segs M a N bs o k Ha HaN H Ho Hok) as (bs1 & H1 & _).
  exact (rdn_grows segs M M' k _ bs1 HG H1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma swrap32_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. Qed.

Lemma wrap32_small : forall z, 0 <= z < 2 ^ 32 -> bv_wrap 32 z = z.
Proof. intros z Hz. apply bv_wrap_small. change (bv_modulus 32) with (2 ^ 32). lia. Qed.

Lemma zbv_srliw_small : forall a k, 0 <= a < 2 ^ 31 -> 0 <= k ->
  v_srliw (Z_to_bv 64 a) k = Z_to_bv 64 (a / 2 ^ k).
Proof.
  intros a k Ha Hk. unfold v_srliw. rewrite u_Z2bv by lia. rewrite (wrap32_small a) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk) as Hp.
  assert (0 <= a / 2 ^ k <= a).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  rewrite swrap32_small by lia. reflexivity.
Qed.

Lemma zbv_sraiw_small : forall a k, 0 <= a < 2 ^ 31 -> 0 <= k ->
  v_sraiw (Z_to_bv 64 a) k = Z_to_bv 64 (a / 2 ^ k).
Proof.
  intros a k Ha Hk. unfold v_sraiw. rewrite u_Z2bv by lia. rewrite (swrap32_small a) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk) as Hp.
  assert (0 <= a / 2 ^ k <= a).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  rewrite swrap32_small by lia. reflexivity.
Qed.

Lemma zbv_mulw_small : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= a * b < 2 ^ 31 ->
  v_mulw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b Ha Hb Hab. unfold v_mulw. rewrite !u_Z2bv by lia. rewrite swrap32_small by lia. reflexivity.
Qed.

Lemma zbv_addw_small : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= a + b < 2 ^ 31 ->
  v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b Ha Hb Hab. unfold v_addw. rewrite !u_Z2bv by lia. rewrite swrap32_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma andi_ones : forall (x : word) k, 0 <= k < 64 ->
  v_andi x (2 ^ k - 1) = Z_to_bv 64 (bv_unsigned x mod 2 ^ k).
Proof.
  intros x k Hk. unfold v_andi. f_equal.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as Hp.
  pose proof (Z.pow_lt_mono_r 2 k 64 ltac:(lia) ltac:(lia)) as Hp64.
  rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma andi_31 : forall x : word, v_andi x 31 = Z_to_bv 64 (bv_unsigned x mod 32).
Proof. intros x. change 31 with (2 ^ 5 - 1). change 32 with (2 ^ 5). apply andi_ones. lia. Qed.
Lemma andi_15 : forall x : word, v_andi x 15 = Z_to_bv 64 (bv_unsigned x mod 16).
Proof. intros x. change 15 with (2 ^ 4 - 1). change 16 with (2 ^ 4). apply andi_ones. lia. Qed.
Lemma andi_3 : forall x : word, v_andi x 3 = Z_to_bv 64 (bv_unsigned x mod 4).
Proof. intros x. change 3 with (2 ^ 2 - 1). change 4 with (2 ^ 2). apply andi_ones. lia. Qed.
Lemma andi_1 : forall x : word, v_andi x 1 = Z_to_bv 64 (bv_unsigned x mod 2).
Proof. intros x. change 1 with (2 ^ 1 - 1) at 1. change 2 with (2 ^ 1) at 2. apply andi_ones. lia. Qed.

(* [comment removed for export] *)
Lemma zbv_seqz : forall a, 0 <= a < 2 ^ 64 ->
  v_sltiu (Z_to_bv 64 a) 1 = Z_to_bv 64 (if a =? 0 then 1 else 0).
Proof.
  intros a Ha. unfold v_sltiu. rewrite u_Z2bv by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec a 0) as [->|Hne]; [reflexivity|].
  replace (a <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_4q_small : forall q r, 0 <= q -> 0 <= r < 4 -> Z.land (4 * q) r = 0.
Proof.
  intros q r Hq Hr. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 2) as [Hl|Hh].
  - replace (4 * q) with (q * 2 ^ 2) by lia. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.eq_dec r 0) as [->|Hr0]; [rewrite Z.bits_0; apply andb_false_r|].
    assert (Hlog : Z.log2 r < i).
    { apply (Z.lt_le_trans _ 2); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 2) with 4. lia. }
    rewrite (Z.bits_above_log2 r i) by lia.
    apply andb_false_r.
Qed.

Lemma lxor_small_3 : forall r, 0 <= r < 4 -> Z.lxor r 3 = 3 - r.
Proof.
  intros r Hr.
  assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3) as [->|[->|[->| ->]]] by lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lxor3_eq : forall p, 0 <= p -> Z.lxor p 3 = p - p mod 4 + (3 - p mod 4).
Proof.
  intros p Hp.
  pose proof (Z.div_mod p 4 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 4 ltac:(lia)) as Hm.
  set (q := p / 4) in *. set (r := p mod 4) in *.
  replace (p - r) with (4 * q) by lia. rewrite Hdm.
  rewrite (Z.add_nocarry_lxor (4 * q) r) by (apply land_4q_small; lia).
  rewrite Z.lxor_assoc, lxor_small_3 by lia.
  symmetry. apply Z.add_nocarry_lxor. apply land_4q_small; lia.
Qed.

Lemma zbv_xori3 : forall p, 0 <= p < 2 ^ 64 ->
  v_xori (Z_to_bv 64 p) 3 = Z_to_bv 64 (p - p mod 4 + (3 - p mod 4)).
Proof.
  intros p Hp. unfold v_xori. rewrite u_Z2bv by lia. change (bv_wrap 64 3) with 3.
  f_equal. apply lxor3_eq. lia.
Qed.

(* [comment removed for export] *)
Lemma flip3_bounds : forall L m p, L mod 4 = 0 -> L <= p < L + 4 * m ->
  L <= p - p mod 4 + (3 - p mod 4) < L + 4 * m.
Proof.
  intros L m p HL Hp.
  pose proof (Z.div_mod p 4 ltac:(lia)). pose proof (Z.mod_pos_bound p 4 ltac:(lia)).
  pose proof (Z.div_mod L 4 ltac:(lia)). nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma depth_mask_278 : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8) ->
  v_andi (v_srl (Z_to_bv 64 278) (Z_to_bv 64 d)) 1 = Z_to_bv 64 1.
Proof. intros d [->|[->|[->| ->]]]; apply bv_eq; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Lemma sllw_m1 : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8) ->
  v_sllw (Z_to_bv 64 (-1)) (Z_to_bv 64 d) = Z_to_bv 64 (2 ^ 64 - 2 ^ d).
Proof. intros d [->|[->|[->| ->]]]; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sllw_m1' : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8) ->
  v_sllw (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 d) = Z_to_bv 64 (2 ^ 64 - 2 ^ d).
Proof. intros d [->|[->|[->| ->]]]; apply bv_eq; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Lemma u_andi_15 : forall x : word, 0 <= bv_unsigned (v_andi x 15) <= 15.
Proof.
  intros x. rewrite andi_15. pose proof (Z.mod_pos_bound (bv_unsigned x) 16 ltac:(lia)).
  rewrite u_Z2bv by lia. lia.
Qed.

Lemma u_andi_3 : forall x : word, 0 <= bv_unsigned (v_andi x 3) <= 3.
Proof.
  intros x. rewrite andi_3. pose proof (Z.mod_pos_bound (bv_unsigned x) 4 ltac:(lia)).
  rewrite u_Z2bv by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma w2l_Z4 : forall v, 0 <= v < 2 ^ 64 -> word_to_le_bytes 4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof. intros v Hv. unfold word_to_le_bytes. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma w2l_Z8 : forall v, 0 <= v < 2 ^ 64 -> word_to_le_bytes 8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof. intros v Hv. unfold word_to_le_bytes. rewrite u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lez4 : forall z, 0 <= z < 2 ^ 32 -> bytes_le_to_Z (Z_to_le_bytes 4 z) = bv_unsigned (Z_to_bv 64 z).
Proof.
  intros z Hz. rewrite bytes_le_Z_to_le by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  rewrite Z.mod_small by lia. rewrite u_Z2bv by lia. reflexivity.
Qed.

Lemma lez8 : forall z, 0 <= z < 2 ^ 64 -> bytes_le_to_Z (Z_to_le_bytes 8 z) = bv_unsigned (Z_to_bv 64 z).
Proof.
  intros z Hz. rewrite bytes_le_Z_to_le by lia. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
  rewrite Z.mod_small by lia. rewrite u_Z2bv by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u_byte64 : forall b : byte, 0 <= bv_unsigned (Z_to_bv 64 (bv_unsigned b)) <= 255.
Proof. intros b. pose proof (u8_range b). rewrite u_Z2bv by lia. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma c_eq_Z_pos : forall a b, 1 <= a <= 2 ^ 64 -> 1 <= b <= 2 ^ 64 ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. rewrite c_eq_Zm.
  destruct (Z.eq_dec a b) as [->|Hne].
  - rewrite !Z.eqb_refl. reflexivity.
  - replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia).
    apply Z.eqb_neq.
    destruct (Z.eq_dec a (2 ^ 64)) as [->|Ha'].
    + rewrite Z.mod_same by lia. rewrite Z.mod_small by lia. lia.
    + rewrite (Z.mod_small a) by lia.
      destruct (Z.eq_dec b (2 ^ 64)) as [->|Hb'].
      * rewrite Z.mod_same by lia. lia.
      * rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac condP :=
  pin; rewrite c_eq_Z_pos by lia;
  first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma andi_7 : forall x : word, v_andi x 7 = Z_to_bv 64 (bv_unsigned x mod 8).
Proof. intros x. change 7 with (2 ^ 3 - 1). change 8 with (2 ^ 3). apply andi_ones. lia. Qed.

(* [comment removed for export] *)
Lemma zbv_snez : forall a, 1 <= a < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 a) = Z_to_bv 64 1.
Proof.
  intros a Ha. unfold v_sltu. rewrite c_ltu_Z by lia.
  replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zbv_sltu_ge : forall a b, 0 <= b <= a -> a < 2 ^ 64 -> v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b Hab Ha. unfold v_sltu. rewrite c_ltu_Z by lia.
  replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zbv_slti0 : forall a, 0 <= a < 2 ^ 63 -> v_slti (Z_to_bv 64 a) 0 = Z_to_bv 64 0.
Proof.
  intros a Ha. unfold v_slti, zsig. rewrite bv_signed_small by (rewrite u_Z2bv by lia; lia).
  rewrite u_Z2bv by lia. replace (a <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sp_slot_al4 : forall sp k, sp mod 16 = 0 -> k mod 4 = 0 -> (sp - k) mod 4 = 0.
Proof.
  intros sp k Hsp Hk.
  apply Z.mod_divide in Hsp; [|lia]. apply Z.mod_divide in Hk; [|lia].
  destruct Hsp as [a Ha]. destruct Hk as [b Hb].
  apply Z.mod_divide; [lia|]. exists (4 * a - b). lia.
Qed.

Lemma zbv_seqz_nz : forall a, 1 <= a < 2 ^ 64 -> v_sltiu (Z_to_bv 64 a) 1 = Z_to_bv 64 0.
Proof. intros a Ha. rewrite zbv_seqz by lia. replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

(* [comment removed for export] *)
Lemma word_addr_al4 : forall data wpl i q, data mod 4 = 0 -> (data + 4 * wpl * i + 4 * q) mod 4 = 0.
Proof.
  intros data wpl i q Hd. replace (data + 4 * wpl * i + 4 * q) with (data + (wpl * i + q) * 4) by lia.
  rewrite Z_mod_plus_full. exact Hd.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

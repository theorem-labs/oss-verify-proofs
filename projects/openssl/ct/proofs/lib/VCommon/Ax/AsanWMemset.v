(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MS_WORDS : list (Z * Z) :=
  [(0x0, 0x00a666b3); (0x4, 0x00f6f693); (0x8, 0x02068063); (0xc, 0x04060863); (0x10, 0x00c50633);
   (0x14, 0x00050693); (0x18, 0x00b68023); (0x1c, 0x00168693); (0x20, 0xfec69ce3); (0x24, 0x0380006f);
   (0x28, 0x02060a63); (0x2c, 0x00c50633); (0x30, 0x00859693); (0x34, 0x00b6e5b3); (0x38, 0x01059693);
   (0x3c, 0x00b6e5b3); (0x40, 0x02059693); (0x44, 0x00b6e5b3); (0x48, 0x00050693); (0x4c, 0x00b6b023);
   (0x50, 0x00b6b423); (0x54, 0x01068693); (0x58, 0xfec6eae3); (0x5c, 0x00008067)]%Z.

Local Ltac dec := wdec.
Lemma DM_0  : decode_any (Z_to_bv 32 0x00a666b3) = Some (Op ALU_OR 13 12 10, 4%Z). Proof. dec. Qed.
Lemma DM_4  : decode_any (Z_to_bv 32 0x00f6f693) = Some (OpImm ALU_AND 13 13 15, 4%Z). Proof. dec. Qed.
Lemma DM_8  : decode_any (Z_to_bv 32 0x02068063) = Some (Branch BC_EQ 13 0 32, 4%Z). Proof. dec. Qed.
Lemma DM_c  : decode_any (Z_to_bv 32 0x04060863) = Some (Branch BC_EQ 12 0 80, 4%Z). Proof. dec. Qed.
Lemma DM_10 : decode_any (Z_to_bv 32 0x00c50633) = Some (Op ALU_ADD 12 10 12, 4%Z). Proof. dec. Qed.
Lemma DM_14 : decode_any (Z_to_bv 32 0x00050693) = Some (OpImm ALU_ADD 13 10 0, 4%Z). Proof. dec. Qed.
Lemma DM_18 : decode_any (Z_to_bv 32 0x00b68023) = Some (Store SZ1 13 11 0, 4%Z). Proof. dec. Qed.
Lemma DM_1c : decode_any (Z_to_bv 32 0x00168693) = Some (OpImm ALU_ADD 13 13 1, 4%Z). Proof. dec. Qed.
Lemma DM_20 : decode_any (Z_to_bv 32 0xfec69ce3) = Some (Branch BC_NE 13 12 8184, 4%Z). Proof. dec. Qed.
Lemma DM_24 : decode_any (Z_to_bv 32 0x0380006f) = Some (Jal 0 56, 4%Z). Proof. dec. Qed.
Lemma DM_28 : decode_any (Z_to_bv 32 0x02060a63) = Some (Branch BC_EQ 12 0 52, 4%Z). Proof. dec. Qed.
Lemma DM_30 : decode_any (Z_to_bv 32 0x00859693) = Some (ShiftImm ALU_SLL 13 11 8, 4%Z). Proof. dec. Qed.
Lemma DM_34 : decode_any (Z_to_bv 32 0x00b6e5b3) = Some (Op ALU_OR 11 13 11, 4%Z). Proof. dec. Qed.
Lemma DM_38 : decode_any (Z_to_bv 32 0x01059693) = Some (ShiftImm ALU_SLL 13 11 16, 4%Z). Proof. dec. Qed.
Lemma DM_40 : decode_any (Z_to_bv 32 0x02059693) = Some (ShiftImm ALU_SLL 13 11 32, 4%Z). Proof. dec. Qed.
Lemma DM_4c : decode_any (Z_to_bv 32 0x00b6b023) = Some (Store SZ8 13 11 0, 4%Z). Proof. dec. Qed.
Lemma DM_50 : decode_any (Z_to_bv 32 0x00b6b423) = Some (Store SZ8 13 11 8, 4%Z). Proof. dec. Qed.
Lemma DM_54 : decode_any (Z_to_bv 32 0x01068693) = Some (OpImm ALU_ADD 13 13 16, 4%Z). Proof. dec. Qed.
Lemma DM_58 : decode_any (Z_to_bv 32 0xfec6eae3) = Some (Branch BC_LTU 13 12 8180, 4%Z). Proof. dec. Qed.
Lemma DM_5c : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr 0 1 0, 4%Z). Proof. dec. Qed.

(* [comment removed for export] *)
Record MSCode (segs : list Segment) (e : Z) : Prop := {
  msc_W : words_ok segs e MS_WORDS = true;
  msc_bnd : (0 <= e /\ e + 0x60 <= 2 ^ 47 /\ e mod 4 = 0)%Z
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint rep (k : nat) (c : Z) : Z :=
  match k with
  | O => 0
  | S k' => c + 256 * rep k' c
  end.

Lemma rep_range : forall k c, 0 <= c < 256 -> 0 <= rep k c < 2 ^ (8 * Z.of_nat k).
Proof.
  induction k as [|k IH]; intros c Hc; cbn [rep].
  - cbn. lia.
  - specialize (IH c Hc). rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia. lia.
Qed.

Lemma le_bytes_rep : forall k c, 0 <= c < 256 -> Z_to_le_bytes k (rep k c) = repeat (Z_to_bv 8 c) k.
Proof.
  induction k as [|k IH]; intros c Hc; [reflexivity|].
  cbn [rep Z_to_le_bytes repeat]. pose proof (rep_range k c Hc).
  f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.add_mod by lia. rewrite Z.mul_comm, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (c + 256 * rep k c) with (rep k c * 256 + c) by lia.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. rewrite Z.add_0_r. apply IH. exact Hc.
Qed.

Lemma land_shiftl_disj : forall a k, 0 <= k -> 0 <= a < 2 ^ k -> Z.land (Z.shiftl a k) a = 0.
Proof.
  intros a k Hk Ha. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.testbit_0_l.
  destruct (Z_lt_le_dec i k) as [Hlt|Hge].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite (Z_testbit_high k a i) by lia. apply andb_false_r.
Qed.

Lemma lor_shiftl : forall a k, 0 <= k -> 0 <= a < 2 ^ k -> Z.lor (Z.shiftl a k) a = a + a * 2 ^ k.
Proof.
  intros a k Hk Ha. rewrite <- Z.lxor_lor by (apply land_shiftl_disj; assumption).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_disj; assumption).
  rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma sll_or_z : forall (a : Z) (sh : bv 6) (k : Z),
  bv_unsigned sh = k -> 0 <= k < 64 -> 0 <= a < 2 ^ k -> a + a * 2 ^ k < 2 ^ 64 ->
  alu64 ALU_OR (alu64 ALU_SLL (Z_to_bv 64 a) (zext 64 sh)) (Z_to_bv 64 a) = Z_to_bv 64 (a + a * 2 ^ k).
Proof.
  intros a sh k Hsh Hk Ha Hb. apply bv_eq. cbv [alu64 alu].
  rewrite bv_or_unsigned, bv_shiftl_unsigned, bv_and_unsigned, bv_zero_extend_unsigned by lia.
  rewrite Hsh. rewrite !bvu_z by (try lia; pose proof (Z.pow_le_mono_r 2 k 64 ltac:(lia) ltac:(lia)); lia).
  replace (Z.land k 63) with k.
  2:{ change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite Z.mod_small by (cbn; lia). reflexivity. }
  rewrite bv_wrap_small.
  - apply lor_shiftl; lia.
  - change (bv_modulus 64) with (2 ^ 64). rewrite Z.shiftl_mul_pow2 by lia.
    pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). nia.
Qed.

Lemma store1_byte : forall (c : word), bv_unsigned c < 256 -> store_bytes SZ1 c = [Z_to_bv 8 (bv_unsigned c)].
Proof.
  intros c Hc. cbn [store_bytes Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  rewrite bv_extract_unsigned, Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma store8_rep : forall (c : Z), 0 <= c < 256 ->
  store_bytes SZ8 (Z_to_bv 64 (rep 8 c)) = repeat (Z_to_bv 8 c) 8.
Proof.
  intros c Hc. cbn [store_bytes]. rewrite bvu_z by (pose proof (rep_range 8 c Hc); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia).
  apply le_bytes_rep. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rep2 : forall c, rep 2 c = c + c * 2 ^ 8. Proof. intros c. cbn [rep]. lia. Qed.
Lemma rep4 : forall c, rep 4 c = rep 2 c + rep 2 c * 2 ^ 16. Proof. intros c. cbn [rep]. lia. Qed.
Lemma rep8 : forall c, rep 8 c = rep 4 c + rep 4 c * 2 ^ 32. Proof. intros c. cbn [rep]. lia. Qed.

(* [comment removed for export] *)
Lemma w2m_repeat : forall k m (a : Z) (v : byte) (x : word),
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  write_to_mem m (Z_to_bv 64 a) (repeat v k) x
  = if ((a <=? bv_unsigned x) && (bv_unsigned x <? a + Z.of_nat k))%bool then Some v else m x.
Proof.
  induction k as [|k IH]; intros m a v x Ha Hak.
  - cbn [repeat write_to_mem]. replace ((a <=? bv_unsigned x) && (bv_unsigned x <? a + Z.of_nat 0))%bool with false
      by (symmetry; apply andb_false_iff; destruct (Z.leb_spec a (bv_unsigned x)); [right; apply Z.ltb_ge; lia | left; reflexivity]).
    reflexivity.
  - cbn [repeat write_to_mem]. rewrite Nat2Z.inj_succ in Hak.
    destruct k as [|k'].
    + cbn [repeat write_to_mem]. pose proof (u64_range x).
      destruct (bv_eqb x (Z_to_bv 64 a)) eqn:E.
      * apply bv_eqb_true_eq in E. subst x. rewrite bvu_z by lia.
        replace ((a <=? a) && (a <? a + Z.of_nat 1))%bool with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        reflexivity.
      * replace ((a <=? bv_unsigned x) && (bv_unsigned x <? a + Z.of_nat 1))%bool with false; [reflexivity|].
        symmetry. apply andb_false_iff. destruct (Z.leb_spec a (bv_unsigned x)); [right|left; reflexivity].
        apply Z.ltb_ge. destruct (Z.eq_dec (bv_unsigned x) a) as [Ex|Ex]; [|lia].
        exfalso. assert (x = Z_to_bv 64 a) by (apply bv_eq; rewrite bvu_z by lia; exact Ex). subst x.
        rewrite bv_eqb_refl in E. discriminate.
    + replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) by (rewrite <- zw_add; reflexivity).
      rewrite IH by lia. cbv beta. pose proof (u64_range x).
      destruct (bv_eqb x (Z_to_bv 64 a)) eqn:E.
      * apply bv_eqb_true_eq in E. subst x. rewrite bvu_z by lia.
        replace ((a + 1 <=? a) && (a <? a + 1 + Z.of_nat (S k')))%bool with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
        replace ((a <=? a) && (a <? a + Z.of_nat (S (S k'))))%bool with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        reflexivity.
      * assert (Hne : bv_unsigned x <> a).
        { intros Ex. assert (x = Z_to_bv 64 a) by (apply bv_eq; rewrite bvu_z by lia; exact Ex). subst x.
          rewrite bv_eqb_refl in E. discriminate. }
        destruct (Z.leb_spec (a + 1) (bv_unsigned x)); destruct (Z.leb_spec a (bv_unsigned x));
          destruct (Z.ltb_spec (bv_unsigned x) (a + 1 + Z.of_nat (S k'))); destruct (Z.ltb_spec (bv_unsigned x) (a + Z.of_nat (S (S k'))));
          cbn [andb]; try reflexivity; lia.
Qed.

Local Close Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record MSR (ms0 ms : machine_state) : Prop := {
  msr_svc : ms_svc_pending ms = None;
  msr_rom : ms_rom ms = ms_rom ms0;
  msr_fregs : ms_fregs ms = ms_fregs ms0;
  msr_fcsr : ms_fcsr ms = ms_fcsr ms0;
  msr_resv : ms_resv ms = ms_resv ms0 \/ ms_resv ms = None;
  msr_regs : forall r, r <> 11 -> r <> 12 -> r <> 13 -> rg ms r = rg ms0 r
}.

(* [comment removed for export] *)
Definition filled (m m0 : word -> option byte) (lo hi : Z) (v : byte) : Prop :=
  forall x : word, ((lo <= bv_unsigned x < hi)%Z -> m x = Some v) /\ (~ (lo <= bv_unsigned x < hi)%Z -> m x = m0 x).

Lemma MSR_refl : forall S, ms_svc_pending S = None -> MSR S S.
Proof.
  intros S H. constructor; [exact H | reflexivity | reflexivity | reflexivity | left; reflexivity | intros; reflexivity].
Qed.

Lemma MSR_setx : forall ms0 S rd v p r m,
  MSR ms0 S -> (rd = 0 \/ rd = 11 \/ rd = 12 \/ rd = 13) -> r = ms_resv S -> m = ms_mem S ->
  MSR ms0 (setx S rd v p r m).
Proof.
  intros ms0 S rd v p r m [H1 H2 H3 H4 H5 H6] Hrd -> ->.
  constructor; [reflexivity | exact H2 | exact H3 | exact H4 | exact H5 |].
  intros r0 R1 R2 R3. rewrite <- (H6 r0 R1 R2 R3).
  destruct Hrd as [ -> |[ -> |[ -> | -> ]]]; [apply rg_setx_x0 | apply rg_setx_other; exact R1
                                     | apply rg_setx_other; exact R2 | apply rg_setx_other; exact R3].
Qed.

Lemma MSR_store : forall ms0 S v p (a : word) r m,
  MSR ms0 S -> r = inval a (ms_resv S) -> MSR ms0 (setx S 0 v p r m).
Proof.
  intros ms0 S v p a r m [H1 H2 H3 H4 H5 H6] ->.
  constructor; [reflexivity | exact H2 | exact H3 | exact H4 | | ].
  - rewrite resv_setx. destruct (inval_cases a (ms_resv S)) as [E|E]; rewrite E; [exact H5 | right; reflexivity].
  - intros r0 R1 R2 R3. rewrite rg_setx_x0. exact (H6 r0 R1 R2 R3).
Qed.

Lemma filled_refl : forall m lo v, filled m m lo lo v.
Proof. intros m lo v x. split; [lia | reflexivity]. Qed.

Lemma filled_grows : forall m m0 lo hi v, filled m m0 lo hi v -> mem_grows m0 m.
Proof.
  intros m m0 lo hi v H x Hx. destruct (H x) as [H1 H2].
  destruct (Z_le_gt_dec lo (bv_unsigned x)); [destruct (Z_lt_le_dec (bv_unsigned x) hi)|].
  - rewrite H1 by lia. discriminate.
  - rewrite H2 by lia. exact Hx.
  - rewrite H2 by lia. exact Hx.
Qed.

Lemma filled_step : forall m m0 (lo i : Z) (k : nat) v,
  (0 <= lo)%Z -> (0 <= i)%Z -> (lo + i + Z.of_nat k <= 2 ^ 64)%Z ->
  filled m m0 lo (lo + i) v -> filled (write_to_mem m (Z_to_bv 64 (lo + i)) (repeat v k)) m0 lo (lo + i + Z.of_nat k) v.
Proof.
  intros m m0 lo i k v Hlo Hi Hk H x. rewrite w2m_repeat by lia. destruct (H x) as [H1 H2].
  destruct (Z.leb_spec (lo + i) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (lo + i + Z.of_nat k)); cbn [andb].
  - split; [reflexivity | lia].
  - split; [lia | intros; apply H2; lia].
  - split; [intros; apply H1; lia | intros; apply H2; lia].
  - split; [intros; apply H1; lia | intros; apply H2; lia].
Qed.

Lemma alu_or_z : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  alu64 ALU_OR (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof.
  intros a b Ha Hb. apply bv_eq. cbv [alu64 alu]. rewrite bv_or_unsigned, !bvu_z by (try apply Z_lor_range; lia).
  reflexivity.
Qed.

Lemma alu_and15_z : forall a : Z, (0 <= a < 2 ^ 64)%Z ->
  alu64 ALU_AND (Z_to_bv 64 a) (sext 64 (@BV 12 15 I)) = Z_to_bv 64 (Z.land a 15).
Proof.
  intros a Ha. rewrite sext64_Z_to_bv. change (bv_signed (@BV 12 15 I)) with 15%Z.
  apply bv_eq. cbv [alu64 alu]. rewrite bv_and_unsigned, !bvu_z by (try apply Z_land_range; lia). reflexivity.
Qed.

Lemma land15_mod : forall a b : Z, (0 <= a)%Z -> (0 <= b)%Z -> Z.land (Z.lor a b) 15 = 0%Z -> (a mod 16 = 0)%Z.
Proof.
  intros a b Ha Hb H. change 16%Z with (2 ^ 4)%Z. rewrite <- Z.land_ones by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.testbit_0_l.
  destruct (Z_lt_le_dec i 4) as [Hlt|Hge].
  - assert (Hb0 : Z.testbit (Z.land (Z.lor a b) 15) i = false) by (rewrite H; apply Z.testbit_0_l).
    rewrite Z.land_spec, Z.lor_spec in Hb0. change 15%Z with (Z.ones 4) in Hb0.
    rewrite Z.testbit_ones in Hb0 by lia. replace ((0 <=? i)%Z && (i <? 4)%Z)%bool with true in Hb0
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite andb_true_r in Hb0. apply orb_false_iff in Hb0 as [-> _]. reflexivity.
  - rewrite Z.testbit_ones by lia. replace ((0 <=? i)%Z && (i <? 4)%Z)%bool with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia). apply andb_false_r.
Qed.

Lemma ret_even : forall w : word, (bv_unsigned w mod 2 = 0)%Z ->
  bv_and (w + sext 64 (@BV 12 0 I)) (bv_not w1) = w.
Proof.
  intros w Hw. rewrite sext64_Z_to_bv. change (bv_signed (@BV 12 0 I)) with 0%Z.
  rewrite <- (Z_to_bv_u w) at 1. rewrite zw_add, Z.add_0_r, Z_to_bv_u.
  apply bv_eq. rewrite bv_and_unsigned, bv_not_unsigned. unfold w1. rewrite bvu_z by lia.
  change (bv_wrap 64 (Z.lnot 1)) with (Z.ones 64 - 1)%Z. pose proof (u64_range w) as Hr.
  change (Z.ones 64 - 1)%Z with (Z.lxor (Z.ones 64) 1).
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - assert (Hq : bv_unsigned w = (2 * (bv_unsigned w / 2))%Z) by (pose proof (Z.div_mod (bv_unsigned w) 2 ltac:(lia)); lia).
    rewrite Hq, Z.testbit_even_0. reflexivity.
  - rewrite (Z.testbit_ones 64 n) by lia. rewrite Z.bits_above_log2 with (a := 1%Z) by (cbn; lia).
    destruct (Z_lt_ge_dec n 64) as [Hlt|Hge].
    + replace ((0 <=? n)%Z && (n <? 64)%Z)%bool with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt || apply Z.leb_le; lia).
      cbn [xorb]. rewrite andb_true_r. reflexivity.
    + replace ((0 <=? n)%Z && (n <? 64)%Z)%bool with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
      cbn [xorb]. rewrite andb_false_r. symmetry.
      destruct (Z.eq_dec (bv_unsigned w) 0) as [E0|E0]; [rewrite E0; apply Z.testbit_0_l|].
      apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
      pose proof (Z.pow_le_mono_r 2 64 n ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac mnorm := rgn; unfold w0; rewrite ?alu_add, ?zw_add, ?zw_add_sext; lits; rewrite ?Z.add_0_r.

Section MSW.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable e : Z.
Hypothesis HC : MSCode segs e.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get segs e MS_WORDS); [exact (msc_W _ _ HC) | inw | lia].

Lemma FM_0  : fetch_word segs (pcw e 0x0)  = Some (Z_to_bv 32 0x00a666b3). Proof. fw. Qed.
Lemma FM_4  : fetch_word segs (pcw e 0x4)  = Some (Z_to_bv 32 0x00f6f693). Proof. fw. Qed.
Lemma FM_8  : fetch_word segs (pcw e 0x8)  = Some (Z_to_bv 32 0x02068063). Proof. fw. Qed.
Lemma FM_c  : fetch_word segs (pcw e 0xc)  = Some (Z_to_bv 32 0x04060863). Proof. fw. Qed.
Lemma FM_10 : fetch_word segs (pcw e 0x10) = Some (Z_to_bv 32 0x00c50633). Proof. fw. Qed.
Lemma FM_14 : fetch_word segs (pcw e 0x14) = Some (Z_to_bv 32 0x00050693). Proof. fw. Qed.
Lemma FM_18 : fetch_word segs (pcw e 0x18) = Some (Z_to_bv 32 0x00b68023). Proof. fw. Qed.
Lemma FM_1c : fetch_word segs (pcw e 0x1c) = Some (Z_to_bv 32 0x00168693). Proof. fw. Qed.
Lemma FM_20 : fetch_word segs (pcw e 0x20) = Some (Z_to_bv 32 0xfec69ce3). Proof. fw. Qed.
Lemma FM_24 : fetch_word segs (pcw e 0x24) = Some (Z_to_bv 32 0x0380006f). Proof. fw. Qed.
Lemma FM_28 : fetch_word segs (pcw e 0x28) = Some (Z_to_bv 32 0x02060a63). Proof. fw. Qed.
Lemma FM_2c : fetch_word segs (pcw e 0x2c) = Some (Z_to_bv 32 0x00c50633). Proof. fw. Qed.
Lemma FM_30 : fetch_word segs (pcw e 0x30) = Some (Z_to_bv 32 0x00859693). Proof. fw. Qed.
Lemma FM_34 : fetch_word segs (pcw e 0x34) = Some (Z_to_bv 32 0x00b6e5b3). Proof. fw. Qed.
Lemma FM_38 : fetch_word segs (pcw e 0x38) = Some (Z_to_bv 32 0x01059693). Proof. fw. Qed.
Lemma FM_3c : fetch_word segs (pcw e 0x3c) = Some (Z_to_bv 32 0x00b6e5b3). Proof. fw. Qed.
Lemma FM_40 : fetch_word segs (pcw e 0x40) = Some (Z_to_bv 32 0x02059693). Proof. fw. Qed.
Lemma FM_44 : fetch_word segs (pcw e 0x44) = Some (Z_to_bv 32 0x00b6e5b3). Proof. fw. Qed.
Lemma FM_48 : fetch_word segs (pcw e 0x48) = Some (Z_to_bv 32 0x00050693). Proof. fw. Qed.
Lemma FM_4c : fetch_word segs (pcw e 0x4c) = Some (Z_to_bv 32 0x00b6b023). Proof. fw. Qed.
Lemma FM_50 : fetch_word segs (pcw e 0x50) = Some (Z_to_bv 32 0x00b6b423). Proof. fw. Qed.
Lemma FM_54 : fetch_word segs (pcw e 0x54) = Some (Z_to_bv 32 0x01068693). Proof. fw. Qed.
Lemma FM_58 : fetch_word segs (pcw e 0x58) = Some (Z_to_bv 32 0xfec6eae3). Proof. fw. Qed.
Lemma FM_5c : fetch_word segs (pcw e 0x5c) = Some (Z_to_bv 32 0x00008067). Proof. fw. Qed.

Section Loop.
Variable model : Model.
Variable K : TSet.
Variable ms0 : machine_state.
Variables (dst n : Z) (c : word).
Hypothesis Hh : m_halted model = None.
Hypothesis Hc : (bv_unsigned c < 256)%Z.
Hypothesis Hdst : (0 <= dst)%Z.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hdn : (dst + n <= 2 ^ 47)%Z.
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis Hsok : store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Z.to_nat n) = true.
Hypothesis Hnl : no_lazy model dst (dst + n).
Hypothesis HK : forall ms', MSR ms0 ms' ->
  filled (ms_mem ms') (ms_mem ms0) dst (dst + n) (Z_to_bv 8 (bv_unsigned c)) ->
  ms_pc_val ms' = rg ms0 1 -> realizes_cfg segs cfg (mkCfg ms' model) K.

Let v := Z_to_bv 8 (bv_unsigned c).

Lemma ms_ret : forall S, MSR ms0 S -> ms_pc_val S = pcw e 0x5c ->
  filled (ms_mem S) (ms_mem ms0) dst (dst + n) v -> realizes_cfg segs cfg (mkCfg S model) K.
Proof.
  intros S HS Hpc Hf.
  eapply rzc_acc; [ exact Hh | exact (msr_svc _ _ HS) | eapply wacc_Jalr; [ rewrite Hpc; exact FM_5c | reflexivity | exact DM_5c ]
                  | apply acc_ok_nil | ].
  apply HK.
  - eapply MSR_setx; [exact HS | left; reflexivity | reflexivity | reflexivity].
  - exact Hf.
  - rewrite pc_setx. rewrite (msr_regs _ _ HS 1) by discriminate. apply ret_even. exact Hra.
Qed.

Lemma sok_sub : forall m (a : Z) k, filled m (ms_mem ms0) dst (dst + (a - dst)) v ->
  (dst <= a)%Z -> (a + Z.of_nat k <= dst + n)%Z -> store_ok segs m (Z_to_bv 64 a) k = true.
Proof.
  intros m a k Hf Ha Hk.
  eapply store_ok_sub; [ | eapply store_ok_mono; [exact (filled_grows _ _ _ _ _ Hf) | exact Hsok] | | ];
    rewrite ?bvu_z by lia; rewrite ?Z2Nat.id by lia; lia.
Qed.

Ltac msr_chain HS :=
  repeat first
   [ (eapply MSR_store; [ | reflexivity ])
   | (eapply MSR_setx; [ | first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
                                 | right; right; right; reflexivity ] | reflexivity | reflexivity ]) ];
  exact HS.

(* [comment removed for export] *)
Lemma byte_loop : forall (d : nat) S (i : Z),
  (n - i = Z.of_nat d)%Z -> (0 <= i < n)%Z ->
  MSR ms0 S -> ms_pc_val S = pcw e 0x18 ->
  rg S 13 = Z_to_bv 64 (dst + i) -> rg S 12 = Z_to_bv 64 (dst + n) -> rg S 11 = c ->
  filled (ms_mem S) (ms_mem ms0) dst (dst + i) v ->
  realizes_cfg segs cfg (mkCfg S model) K.
Proof.
  induction d as [|d IH]; intros S i Hd Hi HS Hpc H13 H12 H11 Hf; [lia|].
  pose proof (msr_svc _ _ HS) as Hsvc.
  (* [comment removed for export] *)
  eapply rzc_acc; [ exact Hh | exact Hsvc | eapply wacc_Store; [ rewrite Hpc; exact FM_18 | reflexivity | exact DM_18 | ] | | ].
  { rewrite H13. mnorm. apply (sok_sub _ (dst + i) 1); [ replace (dst + (dst + i - dst))%Z with (dst + i)%Z by lia; exact Hf | lia | cbn; lia ]. }
  { rewrite H13. mnorm. apply acc_ok_one; rewrite bvu_z by lia; cbn [msz_n Z.of_nat Pos.of_succ_nat];
      [lia | eapply no_lazy_sub; [exact Hnl | lia | lia]]. }
  rewrite Hpc. pcn. rewrite H13, H11. mnorm. rewrite store1_byte by exact Hc.
  (* [comment removed for export] *)
  wst wacc_OpImm FM_1c DM_1c. mnorm. rewrite H13. mnorm.
  (* [comment removed for export] *)
  eapply rzc_acc; [ exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FM_20 | reflexivity | exact DM_20 ] | apply acc_ok_nil | ].
  mnorm. rewrite H12. rewrite branch_ne_z by lia. pcn.
  destruct (Z.eqb_spec (dst + i + 1) (dst + n)) as [Eq|Ne]; cbn [negb]; pcn.
  - (* [comment removed for export] *)
    wst wacc_Jal FM_24 DM_24. apply ms_ret.
    + msr_chain HS.
    + reflexivity.
    + rewrite ?mem_setx. replace (dst + n)%Z with (dst + i + Z.of_nat 1)%Z by lia.
      apply (filled_step _ _ dst i 1); [lia | lia | cbn; lia | exact Hf].
  - apply (IH _ (i + 1)%Z); [lia | lia | msr_chain HS | reflexivity | | | | ].
    + rgn. f_equal. lia.
    + rgn. exact H12.
    + rgn. exact H11.
    + rewrite ?mem_setx. replace (dst + (i + 1))%Z with (dst + i + Z.of_nat 1)%Z by lia.
      apply (filled_step _ _ dst i 1); [lia | lia | cbn; lia | exact Hf].
Qed.

(* [comment removed for export] *)
Lemma word_loop : forall (d : nat) S (i : Z),
  (n - i = 16 * Z.of_nat d)%Z -> (0 <= i < n)%Z ->
  MSR ms0 S -> ms_pc_val S = pcw e 0x4c ->
  rg S 13 = Z_to_bv 64 (dst + i) -> rg S 12 = Z_to_bv 64 (dst + n) -> rg S 11 = Z_to_bv 64 (rep 8 (bv_unsigned c)) ->
  filled (ms_mem S) (ms_mem ms0) dst (dst + i) v ->
  realizes_cfg segs cfg (mkCfg S model) K.
Proof.
  induction d as [|d IH]; intros S i Hd Hi HS Hpc H13 H12 H11 Hf; [lia|].
  pose proof (msr_svc _ _ HS) as Hsvc. pose proof (u64_range c).
  (* [comment removed for export] *)
  eapply rzc_acc; [ exact Hh | exact Hsvc | eapply wacc_Store; [ rewrite Hpc; exact FM_4c | reflexivity | exact DM_4c | ] | | ].
  { rewrite H13. mnorm. apply (sok_sub _ (dst + i) 8); [ replace (dst + (dst + i - dst))%Z with (dst + i)%Z by lia; exact Hf | lia | cbn; lia ]. }
  { rewrite H13. mnorm. apply acc_ok_one; rewrite bvu_z by lia; cbn [msz_n Z.of_nat Pos.of_succ_nat Pos.succ];
      [lia | eapply no_lazy_sub; [exact Hnl | lia | lia]]. }
  rewrite Hpc. pcn. rewrite H13, H11. mnorm. rewrite store8_rep by lia.
  assert (Hf1 : filled (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + i)) (repeat v 8)) (ms_mem ms0) dst (dst + (i + 8)) v).
  { replace (dst + (i + 8))%Z with (dst + i + Z.of_nat 8)%Z by lia. apply filled_step; [lia | lia | cbn; lia | exact Hf]. }
  (* [comment removed for export] *)
  eapply rzc_acc; [ exact Hh | reflexivity | eapply wacc_Store; [ fetch_tac FM_50 | reflexivity | exact DM_50 | ] | | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mnorm. apply (sok_sub _ (dst + i + 8) 8); [ replace (dst + (dst + i + 8 - dst))%Z with (dst + (i + 8))%Z by lia; exact Hf1 | lia | cbn; lia ]. }
  { rgn. rewrite H13. mnorm. apply acc_ok_one; rewrite bvu_z by lia; cbn [msz_n Z.of_nat Pos.of_succ_nat Pos.succ];
      [lia | eapply no_lazy_sub; [exact Hnl | lia | lia]]. }
  pcn. rgn. rewrite H13, H11. mnorm. rewrite store8_rep by lia.
  assert (Hf2 : filled (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + i)) (repeat v 8)) (Z_to_bv 64 (dst + i + 8)) (repeat v 8))
                  (ms_mem ms0) dst (dst + (i + 16)) v).
  { replace (dst + (i + 16))%Z with (dst + (i + 8) + Z.of_nat 8)%Z by lia.
    replace (dst + i + 8)%Z with (dst + (i + 8))%Z by lia. apply filled_step; [lia | lia | cbn; lia | exact Hf1]. }
  (* [comment removed for export] *)
  wst wacc_OpImm FM_54 DM_54. mnorm. rewrite H13. mnorm.
  (* [comment removed for export] *)
  eapply rzc_acc; [ exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FM_58 | reflexivity | exact DM_58 ] | apply acc_ok_nil | ].
  mnorm. rewrite H12. rewrite branch_ltu_z by lia. pcn.
  destruct (Z.ltb_spec (dst + i + 16) (dst + n)) as [Lt|Ge]; pcn.
  - apply (IH _ (i + 16)%Z); [lia | lia | msr_chain HS | reflexivity | | | | ].
    + rgn. f_equal. lia.
    + rgn. exact H12.
    + rgn. exact H11.
    + rewrite ?mem_setx. exact Hf2.
  - apply ms_ret.
    + msr_chain HS.
    + reflexivity.
    + rewrite ?mem_setx. replace (dst + n)%Z with (dst + (i + 16))%Z by lia. exact Hf2.
Qed.

(* [comment removed for export] *)
Lemma ms_entry :
  ms_svc_pending ms0 = None -> ms_pc_val ms0 = pcw e 0 ->
  rg ms0 10 = Z_to_bv 64 dst -> rg ms0 11 = c -> rg ms0 12 = Z_to_bv 64 n ->
  realizes_cfg segs cfg (mkCfg ms0 model) K.
Proof.
  intros Hsvc Hpc H10 H11 H12.
  pose proof (msr_svc _ _ (MSR_refl ms0 Hsvc)) as _. pose proof (u64_range c) as Hcr.
  (* [comment removed for export] *)
  wst wacc_Op FM_0 DM_0. mnorm. rewrite H12, H10. rewrite alu_or_z by lia.
  (* [comment removed for export] *)
  wst wacc_OpImm FM_4 DM_4. mnorm. rewrite alu_and15_z by (pose proof (Z_lor_range n dst); lia).
  (* [comment removed for export] *)
  eapply rzc_acc; [ exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FM_8 | reflexivity | exact DM_8 ] | apply acc_ok_nil | ].
  mnorm. rewrite branch_eq_z by (try lia; pose proof (Z_land_range (Z.lor n dst) 15); pose proof (Z_lor_range n dst); lia). pcn.
  destruct (Z.eqb_spec (Z.land (Z.lor n dst) 15) 0) as [Al|Al]; pcn.
  - (* [comment removed for export] *)
    pose proof (land15_mod n dst Hn Hdst Al) as Hn16.
    eapply rzc_acc; [ exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FM_28 | reflexivity | exact DM_28 ] | apply acc_ok_nil | ].
    mnorm. rewrite H12. rewrite branch_eq_z by lia. pcn.
    destruct (Z.eqb_spec n 0) as [N0|N0]; pcn.
    + apply ms_ret; [msr_chain (MSR_refl ms0 Hsvc) | reflexivity |].
      rewrite ?mem_setx. rewrite N0, Z.add_0_r. apply filled_refl.
    + wst wacc_Op FM_2c DM_10. mnorm. rewrite H10, H12. mnorm.
      wst wacc_ShiftImm FM_30 DM_30. wst wacc_Op FM_34 DM_34. mnorm. rewrite H11.
      rewrite <- (Z_to_bv_u c). rewrite (sll_or_z (bv_unsigned c) _ 8) by (try reflexivity; try lia). rewrite <- rep2.
      wst wacc_ShiftImm FM_38 DM_38. wst wacc_Op FM_3c DM_34. mnorm.
      rewrite (sll_or_z (rep 2 (bv_unsigned c)) _ 16) by (try reflexivity; pose proof (rep_range 2 (bv_unsigned c)); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia).
      rewrite <- rep4.
      wst wacc_ShiftImm FM_40 DM_40. wst wacc_Op FM_44 DM_34. mnorm.
      rewrite (sll_or_z (rep 4 (bv_unsigned c)) _ 32) by (try reflexivity; pose proof (rep_range 4 (bv_unsigned c)); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia).
      rewrite <- rep8.
      wst wacc_OpImm FM_48 DM_14. mnorm. rewrite H10. mnorm.
      apply (word_loop (Z.to_nat (n / 16)) _ 0%Z).
      * pose proof (Z.div_mod n 16 ltac:(lia)). rewrite Z2Nat.id by (apply Z.div_pos; lia). lia.
      * lia.
      * msr_chain (MSR_refl ms0 Hsvc).
      * reflexivity.
      * rgn. f_equal. lia.
      * rgn. reflexivity.
      * rgn. reflexivity.
      * rewrite ?mem_setx. rewrite Z.add_0_r. apply filled_refl.
  - (* [comment removed for export] *)
    eapply rzc_acc; [ exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FM_c | reflexivity | exact DM_c ] | apply acc_ok_nil | ].
    mnorm. rewrite H12. rewrite branch_eq_z by lia. pcn.
    destruct (Z.eqb_spec n 0) as [N0|N0]; pcn.
    + apply ms_ret; [msr_chain (MSR_refl ms0 Hsvc) | reflexivity |].
      rewrite ?mem_setx. rewrite N0, Z.add_0_r. apply filled_refl.
    + wst wacc_Op FM_10 DM_10. mnorm. rewrite H10, H12. mnorm.
      wst wacc_OpImm FM_14 DM_14. mnorm. rewrite H10. mnorm.
      apply (byte_loop (Z.to_nat n) _ 0%Z).
      * rewrite Z2Nat.id by lia. lia.
      * lia.
      * msr_chain (MSR_refl ms0 Hsvc).
      * reflexivity.
      * rgn. f_equal. lia.
      * rgn. reflexivity.
      * rgn. exact H11.
      * rewrite ?mem_setx. rewrite Z.add_0_r. apply filled_refl.
Qed.

End Loop.
End MSW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem internal_memset_sum : forall (segs : list Segment) (cfg : SpuriousCfg) (e : Z), MSCode segs e ->
  forall (ms : machine_state) (model : Model) (K : TSet) (dst n : Z) (c : word),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw e 0 -> m_halted model = None ->
  rg ms 10 = Z_to_bv 64 dst -> rg ms 11 = c -> rg ms 12 = Z_to_bv 64 n ->
  (bv_unsigned c < 256)%Z -> (0 <= dst)%Z -> (0 <= n)%Z -> (dst + n <= 2 ^ 47)%Z ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 dst) (Z.to_nat n) = true ->
  no_lazy model dst (dst + n) ->
  (forall ms', MSR ms ms' ->
     filled (ms_mem ms') (ms_mem ms) dst (dst + n) (Z_to_bv 8 (bv_unsigned c)) ->
     ms_pc_val ms' = rg ms 1 -> realizes_cfg segs cfg (mkCfg ms' model) K) ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros segs cfg e HC ms model K dst n c Hsvc Hpc Hh H10 H11 H12 Hc Hdst Hn Hdn Hra Hsok Hnl HK.
  exact (ms_entry segs cfg e HC model K ms dst n c Hh Hc Hdst Hn Hdn Hra Hsok Hnl HK Hsvc Hpc H10 H11 H12).
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep Arr Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg MRep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sxv (v : Z) : Z := (bv_swrap 32 v) mod 2^64.

Lemma sxv_range v : 0 <= sxv v < 2^64.
Proof. unfold sxv. apply Z.mod_pos_bound. lia. Qed.

Lemma swrap32_eq' z : bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.

Ltac pow_lits :=
  change (2^64)%Z with 18446744073709551616%Z in *;
  change (2^63)%Z with 9223372036854775808%Z in *;
  change (2^33)%Z with 8589934592%Z in *;
  change (2^32)%Z with 4294967296%Z in *;
  change (2^31)%Z with 2147483648%Z in *.
Ltac mlia := pow_lits; Z.div_mod_to_equations; lia.

Lemma sxv_small v : 0 <= v < 2^31 -> sxv v = v.
Proof. intros. unfold sxv. rewrite swrap32_eq'. rewrite (Z.mod_small (v + 2^31)) by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma mod64_mod32 z : (z mod 2^64) mod 2^32 = z mod 2^32.
Proof. apply mod_mod_pow2. lia. Qed.

Lemma sxv_mod32 v : (sxv v) mod 2^32 = v mod 2^32.
Proof. unfold sxv. rewrite mod64_mod32, swrap32_eq'. mlia. Qed.

Lemma sx32_wz_sxv v : 0 <= v < 2^64 -> sx32 (wz v) = wz (sxv v).
Proof. intros. unfold sx32, sxv. rewrite wz_unsigned by lia. unfold wz. rewrite Z_to_bv_mod64. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sextw_sxv v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)) + 0)) = wz (sxv v).
Proof.
  rewrite wz_unsigned by (apply sxv_range). rewrite Z.add_0_r. unfold wz, sxv.
  rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 v mod 2^64))). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.
Lemma sextw_sxv' v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)))) = wz (sxv v).
Proof. rewrite <- (Z.add_0_r (bv_unsigned _)). apply sextw_sxv. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma all_word mword : 0 <= mword ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (mword mod 32)))) + -1))
  = wz (sxv (2 ^ (mword mod 32 + 1) - 1)).
Proof.
  intros. rewrite unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  replace (2 * 2 ^ (mword mod 32)) with (2 ^ (mword mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
  unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  set (y := 2 ^ (mword mod 32 + 1)). rewrite !swrap32_eq'. mlia.
Qed.

Lemma lor_range64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof. intros. apply (zr_lor a b); unfold inr64; lia. Qed.

Lemma land_range64 a b : 0 <= a < 2^64 -> 0 <= b -> 0 <= Z.land a b < 2^64.
Proof. intros. apply (zr_land_l a b); unfold inr64; lia. Qed.

(* [comment removed for export] *)
Lemma sxv_testbit_lo v i : 0 <= v < 2^32 -> 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
  intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.

Lemma sxv_cases v : 0 <= v < 2^32 -> (v < 2^31 /\ sxv v = v) \/ (2^31 <= v /\ sxv v = v + 2^64 - 2^32).
Proof.
  intros. unfold sxv. rewrite swrap32_eq'.
  destruct (Z.lt_ge_cases v (2^31)); [left|right]; split; auto; pow_lits; Z.div_mod_to_equations; nia.
Qed.

(* [comment removed for export] *)
Lemma free_assert_ok freed avail idx :
  0 <= freed < 2^32 -> 0 <= avail < 2^32 -> 0 <= idx < 32 ->
  Z.testbit freed idx = false -> Z.testbit avail idx = false ->
  Z.land (sxv (2^idx)) (Z.lor (sxv freed) (sxv avail)) = 0.
Proof.
  intros HF HA HI TF TA.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64).
  2:{ rewrite (Z.bits_above_log2 (sxv (2^idx))); [reflexivity| apply sxv_range |].
      pose proof (sxv_range (2^idx)). destruct (Z.eq_dec (sxv (2^idx)) 0) as [->|]. cbn; lia.
      apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia]. }
  destruct (Z.lt_ge_cases idx 31).
  - rewrite (sxv_small (2^idx)) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec idx n); [|reflexivity]. subst n. cbn.
    rewrite !sxv_testbit_lo by lia. rewrite TF, TA. reflexivity.
  - assert (idx = 31) by lia. subst idx.
    (* [comment removed for export] *)
    assert (Hlt : forall v, 0 <= v < 2^32 -> Z.testbit v 31 = false -> v < 2^31).
    { intros v Hv Hb. destruct (Z.lt_ge_cases v (2^31)); auto.
      exfalso. assert (Z.testbit v 31 = true); [|congruence].
      rewrite Z.testbit_true by lia. replace (v / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity. }
    pose proof (Hlt freed HF TF). pose proof (Hlt avail HA TA).
    rewrite (sxv_small freed), (sxv_small avail) by lia.
    destruct (Z.lt_ge_cases n 31).
    + replace (Z.testbit (sxv (2^31)) n) with false; [reflexivity|].
      symmetry. rewrite sxv_testbit_lo by lia. rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
    + assert (Lg : forall v, 0 <= v < 2^31 -> Z.testbit v n = false).
      { intros v Hv. destruct (Z.eq_dec v 0) as [->|]. apply Z.bits_0.
        apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 31); [apply Z.log2_lt_pow2; lia| lia]. }
      rewrite (Lg freed), (Lg avail) by lia. apply andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma sxv_zero v : 0 <= v < 2^32 -> sxv v = 0 <-> v = 0.
Proof. intros. destruct (sxv_cases v H) as [[? ->]|[? ->]]; lia. Qed.

(* [comment removed for export] *)
Lemma add_bit_nocarry v idx : 0 <= v < 2^32 -> 0 <= idx < 32 -> Z.testbit v idx = false ->
  v + 2^idx < 2^32.
Proof.
  intros Hv Hi Hb.
  assert (HL : Z.land v (2^idx) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec idx n); [subst; rewrite Hb; reflexivity | apply andb_false_r]. }
  rewrite (Z.add_nocarry_lxor _ _ HL).
  assert (0 <= 2^idx < 2^32) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
  apply Z_bounded_by_bits; [lia | apply Z.lxor_nonneg; lia |].
  intros k Hk. rewrite Z.lxor_spec, (Z_testbit_high 32 v k), (Z_testbit_high 32 (2^idx) k) by lia. reflexivity.
Qed.

Lemma sxv_congr v w : v mod 2^32 = w mod 2^32 -> sxv v = sxv w.
Proof. intros E. unfold sxv. rewrite !swrap32_eq'. f_equal. f_equal. rewrite <- Zplus_mod_idemp_l, E, Zplus_mod_idemp_l. reflexivity. Qed.

Lemma lor_sxv_mod32 f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
  (Z.lor (sxv f) (sxv a)) mod 2^32 = Z.lor f a.
Proof.
  intros. rewrite <- zb_land_mask, zb_land_lor_distr_l, !zb_land_mask, !sxv_mod32, !Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma addw_word x y : Z_to_bv 64 (bv_swrap 32 (x + y)) = wz (sxv (x + y)).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

(* [comment removed for export] *)

Lemma sxv_eq_iff v w : sxv v = sxv w <-> v mod 2^32 = w mod 2^32.
Proof. split; [| apply sxv_congr]. intros E. rewrite <- (sxv_mod32 v), <- (sxv_mod32 w), E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma free_all_test freed avail idx li :
  0 <= freed < 2^32 -> 0 <= avail < 2^32 -> 0 <= idx <= li -> li < 32 ->
  (sxv (sxv (2^idx) + Z.lor (sxv freed) (sxv avail)) = sxv (2^(li + 1) - 1)
   <-> Z.lor freed avail + 2^idx = 2^(li+1) - 1).
Proof.
  intros HF HA HI HL. rewrite sxv_eq_iff.
  rewrite <- Zplus_mod_idemp_r, lor_sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32 by lia.
  assert (X1 : 0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
  assert (XY : 2^idx < 2^(li+1)) by (apply Z.pow_lt_mono_r; lia).
  assert (Y32 : 2^(li+1) <= 2^32) by (apply Z.pow_le_mono_r; lia).
  pose proof (Z_lor_range freed avail ltac:(lia) ltac:(lia)).
  assert (HLr : Z.lor freed avail < 2^32).
  { apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |]. intros k Hk.
    rewrite Z.lor_spec, (Z_testbit_high 32 freed k), (Z_testbit_high 32 avail k) by lia. reflexivity. }
  set (X := 2^idx) in *. set (Y := 2^(li+1)) in *. set (L := Z.lor freed avail) in *.
  clearbody X Y L. rewrite (Z.mod_small X) by lia. mlia.
Qed.

(* [comment removed for export] *)
Lemma le4_congr (a b : word) : bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> le4 a = le4 b.
Proof. intros E. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia). rewrite E. reflexivity. Qed.

Lemma free_store_val freed idx : 0 <= freed < 2^32 -> 0 <= idx < 32 -> Z.testbit freed idx = false ->
  le4 (wz (sxv (sxv (2^idx) + sxv freed))) = le4 (wz (freed + 2^idx)).
Proof.
  intros. pose proof (add_bit_nocarry freed idx ltac:(lia) ltac:(lia) ltac:(eassumption)).
  assert (0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
  apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
  rewrite sxv_mod32, <- Zplus_mod_idemp_r, sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32, !Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)

Lemma sllw2_word e : 0 <= e ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (e mod 32))) = wz (sxv (2 ^ (e mod 32 + 1))).
Proof.
  intros. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  replace (2 * 2 ^ (e mod 32)) with (2 ^ (e mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma addiw_m1_word y : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv y)) + -1)) = wz (sxv (y - 1)).
Proof.
  rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.

Lemma rw_cells_congr segs m A cs cs' :
  cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' ->
  rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof. intros EB ES WF [[_ B] W]. split; [split; [exact WF| rewrite <- EB; exact B] | rewrite <- ES; exact W]. Qed.

Lemma le1_neg1 : le1 (Z_to_bv 64 (-1)) = [b8 255].
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)

Definition frozen (P : Prop) : Prop := P.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wr_at_sub : forall segs m A n A' n',
  wr_at segs m A n -> A <= A' -> A' + n' <= A + n -> wr_at segs m A' n'.
Proof.
  (intros segs m A n A' n'; (first [ intro dR_6; dand3 dR_6 as H0 H1 H | intros (H0 & H1 & H) ]); intros LA LB). split; [lia|]. split; [lia|].
  intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed.

Lemma rw_cells_prefix : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1.
Proof.
  intros segs m A cs1 cs2 [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 _].
  split; [split; [exact WF1 | exact B1] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

Lemma bytes_at_at : forall segs m a a' bs, bytes_at segs m a bs -> a = a' -> bytes_at segs m a' bs.
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_of_bytes : forall segs m A cs,
  cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
Proof. intros. split; [split|]; assumption. Qed.

(* [comment removed for export] *)
Lemma area_of_slot : forall (a : aptr) k, snd a mod 4096 = 0 -> 0 <= k < 101 ->
  area_of (aadd a (24 + 40 * k)) = a.
Proof.
  intros [ar ao] k Hm Hk. unfold area_of, aadd. cbn [fst snd] in *. f_equal.
  replace (ao + (24 + 40 * k)) with ((24 + 40 * k) + (ao / 4096) * 4096) by (Z.div_mod_to_equations; nia).
  rewrite Z.mod_add, Z.mod_small by lia. Z.div_mod_to_equations; nia.
Qed.

Lemma page_off_mod : forall b o x, b mod 4096 = 0 -> o mod 4096 = 0 -> 0 <= x < 4096 -> (b + o + x) mod 4096 = x.
Proof.
  intros b o x Hb Ho Hx.
  replace (b + o + x) with (x + (b / 4096 + o / 4096) * 4096) by (Z.div_mod_to_equations; nia).
  rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.

Lemma base16_mod : forall b po, b mod 4096 = 0 -> po mod 16 = 0 -> (b + po) mod 16 = 0.
Proof.
  intros b po Hb Hp. replace (b + po) with ((b / 4096) * 256 * 16 + (po / 16) * 16) by (Z.div_mod_to_equations; lia).
  rewrite <- Z.mul_add_distr_r, Z.mod_mul. reflexivity. lia.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma optr_eqb_refl : forall q : aptr, optr_eqb (Some q) (Some q) = true.
Proof. intros [qa qb]. unfold optr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem := word -> option byte.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pres_except (C : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> ~ C a ->
    m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Lemma pres_except_refl C m : pres_except C m m.
Proof. intros a _ _; auto. Qed.
Lemma pres_except_trans C m1 m2 m3 : pres_except C m1 m2 -> pres_except C m2 m3 -> pres_except C m1 m3.
Proof. intros H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma pres_except_mono (C C' : Z -> Prop) m m' : pres_except C m m' -> (forall a, C a -> C' a) -> pres_except C' m m'.
Proof. intros H HC a Ha Hc. apply H; [exact Ha|]. intros Hc'. apply Hc, HC, Hc'. Qed.

(* [comment removed for export] *)
Lemma pres_except_of_munch C W m m' :
  munch W m m' -> wmono rsegs m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> pres_except C m m'.
Proof.
  intros MU WM HW a Ha Hc. split.
  - apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
  - apply WM.
Qed.

Lemma pres_except_bytes_at C m m' A bs :
  pres_except C m m' -> bytes_at rsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) ->
  bytes_at rsegs m' A bs.
Proof.
  (intros HP; (first [ intro dR_7; dand3 dR_7 as H0 H1 HB | intros (H0 & H1 & HB) ]); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma pres_except_wr_at C m m' A n :
  pres_except C m m' -> wr_at rsegs m A n -> (forall a, A <= a < A + n -> ~ C a) -> wr_at rsegs m' A n.
Proof.
  (intros HP; (first [ intro dR_8; dand3 dR_8 as H0 H1 HW | intros (H0 & H1 & HW) ]); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W, HW, Hi.
Qed.

Lemma pres_except_rw_cells C m m' A cs :
  pres_except C m m' -> rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) ->
  rw_cells rsegs m' A cs.
Proof.
  intros HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply pres_except_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply pres_except_wr_at; eauto.
Qed.

Lemma pres_except_stk C m m' lo hi :
  pres_except C m m' -> stk rsegs m lo hi -> (forall a, lo <= a < hi -> ~ C a) -> stk rsegs m' lo hi.
Proof.
  (intros HP; (first [ intro dR_9; dand3 dR_9 as H0 H1 HW | intros (H0 & H1 & HW) ]); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
Definition alloc_fp (K : rkind -> Prop) (st1 : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ errno_addr (Z_to_bv 64 0x42158) <= a < errno_addr (Z_to_bv 64 0x42158) + 4
  \/ CTX <= a < CTX + 928
  \/ exists rid r, (s_regions st1) !! rid = Some r /\ K (r_kind r) /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).
  (* [comment removed for export] *)


(* [comment removed for export] *)
Definition optr_in (P : N -> Prop) (p : optr) : Prop :=
  match p with Some q => P (fst q) | None => True end.

Definition ptrs_in (P : N -> Prop) (st : mstate) : Prop :=
  let c := ctx st in
  optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
  /\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
  /\ (forall sc, optr_in P (active st sc))
  /\ match c_brk c with BrkLive rid _ => P rid | _ => True end
  /\ (forall g, optr_in P (m_prev (get_meta_rec st g)) /\ optr_in P (m_next (get_meta_rec st g))
             /\ optr_in P (m_mem (get_meta_rec st g)))
  /\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
  /\ (forall b gh, (s_groups st) !! b = Some gh -> P (fst b) /\ optr_in P (g_meta gh)).

Lemma ptrs_in_mono (P P' : N -> Prop) st : (forall r, P r -> P' r) -> ptrs_in P st -> ptrs_in P' st.
Proof.
  (intros HP; (first [ intro dR_10; dand10 dR_10 as H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 | intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) ])).
  assert (OM : forall p, optr_in P p -> optr_in P' p) by (intros [q|]; cbn; auto).
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [intros sc; apply OM, H6|]. split; [destruct (c_brk (ctx st)); auto|].
  split; [intros g; (first [ pose proof ((H8 g)) as dR_1; dand3 dR_1 as X1 X2 X3 | destruct (H8 g) as (X1 & X2 & X3) ]); auto|].
  split; [intros a ar Ha; destruct (H9 a ar Ha); auto|].
  intros b gh Hb; destruct (H10 b gh Hb); auto.
Qed.

(* [comment removed for export] *)
Record am_rel (st st1 : mstate) (mo : optr) : Prop := mkAMR {
  amr_active : forall sc, active st1 sc = active st sc;
  amr_usage : forall sc, usage st1 sc = usage st sc;
  amr_bounces : forall i, bounces st1 i = bounces st i;
  amr_unmap_seq : forall i, unmap_seq st1 i = unmap_seq st i;
  amr_seq : c_seq (ctx st1) = c_seq (ctx st);
  amr_counter : c_mmap_counter (ctx st1) = c_mmap_counter (ctx st);
  amr_groups : s_groups st1 = s_groups st;
  amr_slots : s_slots st1 = s_slots st;
  amr_shadow : s_shadow st1 = s_shadow st;
  amr_tick : s_tick st1 = s_tick st;
  amr_reserved : s_reserved st1 = s_reserved st;
  (* [comment removed for export] *)
  amr_metas : forall g, Some g <> mo ->
      (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) ->
      get_meta_rec st1 g = get_meta_rec st g;
  (* [comment removed for export] *)
  amr_result : forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m;
  (* [comment removed for export] *)
  amr_regions : forall rid r, (s_regions st) !! rid = Some r ->
      exists r', (s_regions st1) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
                 /\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
  amr_new : forall rid r', (s_regions st1) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
  amr_next_rid : (s_next_rid st <= s_next_rid st1)%N;
  amr_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
  (* [comment removed for export] *)
  amr_ptrs : forall P : N -> Prop,
      (forall rid r, (s_regions st1) !! rid = Some r -> r_kind r <> RKGroup -> P rid) ->
      ptrs_in P st -> ptrs_in P st1;
  (* [comment removed for export] *)
  amr_fresh : forall rid, (s_next_rid st1 <= rid)%N -> (s_regions st1) !! rid = None /\ (s_shadow st1) !! rid = (s_shadow st) !! rid
}.

Definition AM_STACK : Z := 144.   (* [comment removed for export] *)

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Definition fresh_addr (st : mstate) (a : Z) : Prop :=
  a < alloc_ceiling /\ ranges_free (live_ranges st) a 1 = true.

Lemma ranges_free_In l a n b k : ranges_free l a n = true -> In (b, k) l -> a + n <= b \/ b + k <= a.
Proof.
  intros H HI. unfold ranges_free in H. apply (proj1 (forallb_forall _ _) H) in HI. cbn [fst snd] in HI.
  unfold iv_disjoint in HI. apply Bool.orb_prop in HI. destruct HI as [X|X]; apply Z.leb_le in X; lia.
Qed.

Lemma ranges_free_intro l a n : (forall b k, In (b, k) l -> a + n <= b \/ b + k <= a) -> ranges_free l a n = true.
Proof.
  intros H. unfold ranges_free. apply (proj2 (forallb_forall _ _)). intros [b k] HI. cbn [fst snd].
  unfold iv_disjoint. destruct (H b k HI) as [X|X]; [rewrite (proj2 (Z.leb_le _ _) X); reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) X). apply Bool.orb_true_r.
Qed.

Lemma ranges_free_sub l a n a' n' : ranges_free l a n = true -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> ranges_free l a' n' = true.
Proof.
  intros H H1 H2 H3. apply ranges_free_intro. intros b k HI. pose proof (ranges_free_In l a n b k H HI). lia.
Qed.

Lemma In_live_ranges st rid r : (s_regions st) !! rid = Some r ->
  In (region_live_range r) (live_ranges st).
Proof.
  intros Hr. unfold live_ranges. apply in_or_app. right. apply in_map_iff. exists (rid, r). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma fresh_live_region st a rid r : fresh_addr st a -> (s_regions st) !! rid = Some r ->
  a + 1 <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= a.
Proof.
  intros [_ FR] Hr. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ FR HI); lia).
Qed.

(* [comment removed for export] *)
Lemma fresh_image st a : fresh_addr st a -> s_reserved st = p0_reserved -> a < 0x10000 \/ 0x63000 <= a.
Proof.
  intros [_ FR] RS. unfold live_ranges in FR. rewrite RS in FR.
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). lia.
Qed.

(* [comment removed for export] *)
Lemma fresh_addr_anti st st' a :
  s_reserved st' = s_reserved st ->
  (forall rid r, (s_regions st) !! rid = Some r ->
     exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  fresh_addr st' a -> fresh_addr st a.
Proof.
  intros RS HR [FC FR]. split; [exact FC|]. apply ranges_free_intro. intros b k HI.
  unfold live_ranges in HI. apply in_app_or in HI. destruct HI as [HI|HI].
  - apply (ranges_free_In (live_ranges st') a 1 b k FR). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI.
  - apply in_map_iff in HI. (first [ dand3 HI as [rid r] E HI | destruct HI as ([rid r] & E & HI) ]). cbn [snd] in E.
    apply (proj2 (list_elem_of_In _ _)) in HI. apply elem_of_map_to_list in HI.
    (first [ pose proof ((HR rid r HI)) as dR_3; dex1 dR_3 as r'; dand4 dR_3 as Hr' K' B' L' | pose proof ((HR rid r HI)) as dR_3; dand5 dR_3 as r' Hr' K' B' L' | destruct (HR rid r HI) as (r' & Hr' & K' & B' & L') ]).
    pose proof (In_live_ranges st' rid r' Hr') as HI'.
    assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
    { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
    unfold region_live_range in HI', E. rewrite K', B' in HI'.
    destruct (r_kind r); inversion E; subst; (pose proof (ranges_free_In _ _ _ _ _ FR HI'); lia).
Qed.

End CEIL.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap_word x : Z_to_bv 64 (bv_swrap 32 x) = wz (sxv x).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

Lemma sxv_testbit_lo' v i : 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
  intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. apply Z.mod_pow2_bits_low. lia.
Qed.

(* [comment removed for export] *)
Lemma sxv_cases' v : let u := v mod 2^32 in
  (u < 2^31 /\ sxv v = u) \/ (2^31 <= u /\ sxv v = u + 2^64 - 2^32).
Proof.
  cbv zeta. pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
  rewrite <- (sxv_congr (v mod 2^32) v) by (apply Z.mod_mod; lia).
  destruct (sxv_cases (v mod 2^32) ltac:(lia)); tauto.
Qed.

Lemma testbit_31_mod32 v : Z.testbit v 31 = (2^31 <=? v mod 2^32).
Proof.
  rewrite <- (Z.mod_pow2_bits_low v 32 31) by lia. rewrite Z.testbit_eqb by lia.
  pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
  destruct (Z.leb_spec (2^31) (v mod 2^32)).
  - replace (v mod 2^32 / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
  - rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma sxv_testbit_hi v i : 31 <= i < 64 -> Z.testbit (sxv v) i = Z.testbit v 31.
Proof.
  intros Hi. rewrite testbit_31_mod32. rewrite Z.testbit_eqb by lia.
  assert (P31 : 2^31 <= 2^i) by (apply Z.pow_le_mono_r; lia).
  assert (P63 : 2^i <= 2^63) by (apply Z.pow_le_mono_r; lia).
  assert (E64 : 2^64 = 2^(64-i) * 2^i) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (E2 : 2^(64-i) = 2 * 2^(64-i-1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (P1 : 1 <= 2^(64-i-1)) by (apply Z.pow_le_mono_r with (b:=0) in Hi || idtac; apply (Z.pow_le_mono_r 2 0); lia).
  destruct (sxv_cases' v) as [[Hu E]|[Hu E]]; rewrite E.
  - rewrite Z.div_small by lia. cbn. symmetry. apply Z.leb_gt. lia.
  - pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
    replace ((v mod 2^32 + 2^64 - 2^32) / 2^i) with (2^(64-i) - 1) by (Z.div_mod_to_equations; nia).
    rewrite E2. replace (2 * 2^(64-i-1) - 1) with (1 + (2^(64-i-1) - 1) * 2) by lia.
    rewrite Z.mod_add by lia. cbn. symmetry. apply Z.leb_le. lia.
Qed.

Lemma sxv_testbit_high v i : 64 <= i -> Z.testbit (sxv v) i = false.
Proof.
  intros. pose proof (sxv_range v). destruct (Z.eq_dec (sxv v) 0) as [->|]. apply Z.bits_0.
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed.

Lemma sxv_land a b : Z.land (sxv a) (sxv b) = sxv (Z.land a b).
Proof.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 32); [| destruct (Z.lt_ge_cases i 64)].
  - rewrite !sxv_testbit_lo' by lia. symmetry. apply Z.land_spec.
  - rewrite !sxv_testbit_hi by lia. rewrite Z.land_spec. reflexivity.
  - rewrite !sxv_testbit_high by lia. reflexivity.
Qed.

Lemma sxv_idem v : sxv (sxv v) = sxv v.
Proof. apply sxv_congr. apply sxv_mod32. Qed.

(* [comment removed for export] *)
Lemma land_opp_odd a : Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma land_opp_even a : Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (- a).
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite !Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

Lemma lowbit_pow2 : forall m, 0 < m -> exists k, 0 <= k /\ Z.land m (- m) = 2 ^ k /\ 2 ^ k <= m.
Proof.
  intros m Hm.
  pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
  cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
  intros x IH Hx0 Hx.
  destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
  - (first [ pose proof ((IH a ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as k; dand3 dR_4 as Hk E L | pose proof ((IH a ltac:(lia) ltac:(lia))) as dR_4; dand4 dR_4 as k Hk E L | destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L) ]).
    exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
  - exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.

Lemma land_opp_pow2 k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
  intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
  subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lowbit_nonzero m : 0 < m -> exists k, 0 <= k /\ lowbit m = 2 ^ k /\ 2 ^ k <= m.
Proof. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.

Lemma lowbit_0 : lowbit 0 = 0.
Proof. reflexivity. Qed.

Lemma ctz32_pow2 k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma negw_and_lowbit v : 0 <= v < 2^32 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv v)))))) (bv_unsigned (wz (sxv v))))
  = wz (sxv (lowbit v)).
Proof.
  intros Hv. rewrite swrap_word. rewrite !wz_unsigned by apply sxv_range.
  rewrite sxv_land. unfold lowbit, wz. f_equal.
  rewrite (Z.land_comm v (- v)).
  transitivity (sxv (Z.land (sxv (0 - sxv v)) (sxv v))); [rewrite sxv_land, sxv_idem; reflexivity|].
  transitivity (sxv (Z.land (sxv (- v)) (sxv v))); [| rewrite sxv_land, sxv_idem; reflexivity].
  f_equal. f_equal. apply sxv_congr.
  rewrite <- Zminus_mod_idemp_r, sxv_mod32, Zminus_mod_idemp_r. replace (0 - v) with (- v) by lia. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)



(* [comment removed for export] *)

Lemma le4_avail_sub a b : 0 <= b <= a -> a < 2^32 ->
  le4 (wz (sxv (sxv a - sxv b))) = le4 (wz (a - b)).
Proof.
  intros. apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
  rewrite sxv_mod32, <- Zminus_mod_idemp_r, sxv_mod32, <- Zminus_mod_idemp_l, sxv_mod32, Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rDB32 : Z := 125613361.   (* [comment removed for export] *)
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.

Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof. unfold rdbi. pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

Definition rdebruijn_bytes : list byte :=
  Eval vm_compute in (match image_bytes rsegs DEBRUIJN 32 with Some bs => bs | None => [] end).

Lemma rdebruijn_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m DEBRUIJN [CB 32 rdebruijn_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold DEBRUIJN; lia | unfold DEBRUIJN; cbn; lia]. Qed.

Lemma rdebruijn_read : forall m k, mem_inv rsegs m -> 0 <= k < 32 ->
  ov_read_bytes rsegs m (wa (DEBRUIJN + rdbi k)) 1 = Some [b8 k].
Proof.
  intros m k MI Hk.
  destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  pose proof (rdbi_range k) as R.
  rewrite (bytes_at_read rsegs m DEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
  assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
  (first [ dex1 Hn as n; destruct Hn as [-> Hn] | dand3 Hn as n -> Hn | destruct Hn as (n & -> & Hn) ]).
  Ltac solve_db := vm_compute; reflexivity.
  do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

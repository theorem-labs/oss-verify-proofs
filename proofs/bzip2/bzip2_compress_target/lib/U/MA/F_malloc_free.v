(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac Image ZBridge SysStep SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Definition AGP : Z := 0x1a800.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sxv (v : Z) : Z := (bv_swrap 32 v) mod 2^64.

Lemma sxv_range v : 0 <= sxv v < 2^64.
Proof. unfold sxv. apply Z.mod_pos_bound. lia. Qed.

Lemma swrap32_eq' z : bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.
End ACeilS1.


Ltac pow_lits :=
  change (2^64)%Z with 18446744073709551616%Z in *;
  change (2^63)%Z with 9223372036854775808%Z in *;
  change (2^33)%Z with 8589934592%Z in *;
  change (2^32)%Z with 4294967296%Z in *;
  change (2^31)%Z with 2147483648%Z in *.
Ltac mlia := pow_lits; Z.div_mod_to_equations; lia.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


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
  intros. pose proof (add_bit_nocarry freed idx ltac:(lia) ltac:(lia) ltac:(assumption)).
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
End ACeilS2.


(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          let E := fresh "EQ" m' in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
          clear HB; try rename H' into H
        end
    end
  end.
Section ACeilS3. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Definition frozen (P : Prop) : Prop := P.

(* [comment removed for export] *)

(* [comment removed for export] *)
End ACeilS3.


(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.
Section ACeilS4. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wr_at_sub : forall segs m A n A' n',
  wr_at segs m A n -> A <= A' -> A' + n' <= A + n -> wr_at segs m A' n'.
Proof.
  (intros segs m A n A' n'; cps_intros (H0 & H1 & H); intros LA LB). split; [lia|]. split; [lia|].
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
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma optr_eqb_refl : forall q : aptr, optr_eqb (Some q) (Some q) = true.
Proof. intros [qa qb]. unfold optr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS4.

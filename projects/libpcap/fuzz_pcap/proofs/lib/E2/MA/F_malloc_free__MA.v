(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Image ZBridge SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_malloc_free.
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MallocRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Definition sxv (v : Z) : Z := (bv_swrap 32 v) mod 2^64.

#[using="Type"] Lemma sxv_range v : 0 <= sxv v < 2^64.
Proof. unfold sxv. apply Z.mod_pos_bound. lia. Qed.

#[using="Type"] Lemma swrap32_eq' z : bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.
End PORT.
End WithCeil.


Ltac pow_lits :=
  change (2^64)%Z with 18446744073709551616%Z in *;
  change (2^63)%Z with 9223372036854775808%Z in *;
  change (2^33)%Z with 8589934592%Z in *;
  change (2^32)%Z with 4294967296%Z in *;
  change (2^31)%Z with 2147483648%Z in *.
Ltac mlia := pow_lits; Z.div_mod_to_equations; lia.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma sxv_small v : 0 <= v < 2^31 -> sxv v = v.
Proof. intros. unfold sxv. rewrite swrap32_eq'. rewrite (Z.mod_small (v + 2^31)) by lia. rewrite Z.mod_small by lia. lia. Qed.

#[using="Type"] Lemma mod64_mod32 z : (z mod 2^64) mod 2^32 = z mod 2^32.
Proof. apply mod_mod_pow2. lia. Qed.

#[using="Type"] Lemma sxv_mod32 v : (sxv v) mod 2^32 = v mod 2^32.
Proof. unfold sxv. rewrite mod64_mod32, swrap32_eq'. mlia. Qed.

#[using="Type"] Lemma sx32_wz_sxv v : 0 <= v < 2^64 -> sx32 (wz v) = wz (sxv v).
Proof. intros. unfold sx32, sxv. rewrite wz_unsigned by lia. unfold wz. rewrite Z_to_bv_mod64. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sextw_sxv v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)) + 0)) = wz (sxv v).
Proof.
  rewrite wz_unsigned by (apply sxv_range). rewrite Z.add_0_r. unfold wz, sxv.
  rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 v mod 2^64))). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.
#[using="Type"] Lemma sextw_sxv' v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)))) = wz (sxv v).
Proof. rewrite <- (Z.add_0_r (bv_unsigned _)). apply sextw_sxv. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma self_word b3 : 0 <= b3 < 256 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 b3))) 31)) mod 32)))
  = wz (sxv (2 ^ (Z.land b3 31))).
Proof.
  intros. rewrite zxb_b8, (wz_unsigned b3) by lia.
  assert (0 <= Z.land b3 31 < 32).
  { split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite (wz_unsigned (Z.land b3 31)) by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma all_word mword : 0 <= mword ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (mword mod 32)))) + -1))
  = wz (sxv (2 ^ (mword mod 32 + 1) - 1)).
Proof.
  intros. rewrite unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  replace (2 * 2 ^ (mword mod 32)) with (2 ^ (mword mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
  unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  set (y := 2 ^ (mword mod 32 + 1)). rewrite !swrap32_eq'. mlia.
Qed.

#[using="Type"] Lemma lor_range64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof. intros. apply (zr_lor a b); unfold inr64; lia. Qed.

#[using="Type"] Lemma land_range64 a b : 0 <= a < 2^64 -> 0 <= b -> 0 <= Z.land a b < 2^64.
Proof. intros. apply (zr_land_l a b); unfold inr64; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sxv_testbit_lo v i : 0 <= v < 2^32 -> 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
  intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.

#[using="Type"] Lemma sxv_cases v : 0 <= v < 2^32 -> (v < 2^31 /\ sxv v = v) \/ (2^31 <= v /\ sxv v = v + 2^64 - 2^32).
Proof.
  intros. unfold sxv. rewrite swrap32_eq'.
  destruct (Z.lt_ge_cases v (2^31)); [left|right]; split; auto; pow_lits; Z.div_mod_to_equations; nia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma free_assert_ok freed avail idx :
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
#[using="Type"] Lemma sxv_zero v : 0 <= v < 2^32 -> sxv v = 0 <-> v = 0.
Proof. intros. destruct (sxv_cases v H) as [[? ->]|[? ->]]; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma add_bit_nocarry v idx : 0 <= v < 2^32 -> 0 <= idx < 32 -> Z.testbit v idx = false ->
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

#[using="Type"] Lemma sxv_congr v w : v mod 2^32 = w mod 2^32 -> sxv v = sxv w.
Proof. intros E. unfold sxv. rewrite !swrap32_eq'. f_equal. f_equal. rewrite <- Zplus_mod_idemp_l, E, Zplus_mod_idemp_l. reflexivity. Qed.

#[using="Type"] Lemma lor_sxv_mod32 f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
  (Z.lor (sxv f) (sxv a)) mod 2^32 = Z.lor f a.
Proof.
  intros. rewrite <- zb_land_mask, zb_land_lor_distr_l, !zb_land_mask, !sxv_mod32, !Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma addw_word x y : Z_to_bv 64 (bv_swrap 32 (x + y)) = wz (sxv (x + y)).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

#[using="Type"] Lemma wz_inj a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> wz a = wz b -> a = b.
Proof. intros Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !wz_unsigned in E by lia. exact E. Qed.

#[using="Type"] Lemma sxv_eq_iff v w : sxv v = sxv w <-> v mod 2^32 = w mod 2^32.
Proof. split; [| apply sxv_congr]. intros E. rewrite <- (sxv_mod32 v), <- (sxv_mod32 w), E. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma free_all_test freed avail idx li :
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
#[using="Type"] Lemma le4_congr (a b : word) : bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> le4 a = le4 b.
Proof. intros E. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia). rewrite E. reflexivity. Qed.

#[using="Type"] Lemma free_store_val freed idx : 0 <= freed < 2^32 -> 0 <= idx < 32 -> Z.testbit freed idx = false ->
  le4 (wz (sxv (sxv (2^idx) + sxv freed))) = le4 (wz (freed + 2^idx)).
Proof.
  intros. pose proof (add_bit_nocarry freed idx ltac:(lia) ltac:(lia) ltac:(assumption)).
  assert (0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
  apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
  rewrite sxv_mod32, <- Zplus_mod_idemp_r, sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32, !Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma self_word' b3 : 0 <= b3 < 256 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 (Z.land b3 31)) mod 32)))
  = wz (sxv (2 ^ (Z.land b3 31))).
Proof.
  intros.
  assert (0 <= Z.land b3 31 < 32).
  { split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite (wz_unsigned (Z.land b3 31)) by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

#[using="Type"] Lemma sllw2_word e : 0 <= e ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (e mod 32))) = wz (sxv (2 ^ (e mod 32 + 1))).
Proof.
  intros. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  replace (2 * 2 ^ (e mod 32)) with (2 ^ (e mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

#[using="Type"] Lemma addiw_m1_word y : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv y)) + -1)) = wz (sxv (y - 1)).
Proof.
  rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.

#[using="Type"] Lemma rw_cells_congr segs m A cs cs' :
  cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' ->
  rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof. intros EB ES WF [[_ B] W]. split; [split; [exact WF| rewrite <- EB; exact B] | rewrite <- ES; exact W]. Qed.

#[using="Type"] Lemma le1_neg1 : le1 (Z_to_bv 64 (-1)) = [b8 255].
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

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

Definition frozen (P : Prop) : Prop := P.

Definition free_W (sp : word) (P G : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.

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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_sub : forall segs m A n A' n',
  wr_at segs m A n -> A <= A' -> A' + n' <= A + n -> wr_at segs m A' n'.
Proof.
  intros segs m A n A' n' (H0 & H1 & H) LA LB. split; [lia|]. split; [lia|].
  intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed.

#[using="Type"] Lemma rw_cells_prefix : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1.
Proof.
  intros segs m A cs1 cs2 [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 _].
  split; [split; [exact WF1 | exact B1] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

#[using="Type"] Lemma bytes_at_at : forall segs m a a' bs, bytes_at segs m a bs -> a = a' -> bytes_at segs m a' bs.
Proof. intros; subst; assumption. Qed.

#[using="Type"] Lemma rw_cells_of_bytes : forall segs m A cs,
  cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
Proof. intros. split; [split|]; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma area_of_slot : forall (a : aptr) k, snd a mod 4096 = 0 -> 0 <= k < 101 ->
  area_of (aadd a (24 + 40 * k)) = a.
Proof.
  intros [ar ao] k Hm Hk. unfold area_of, aadd. cbn [fst snd] in *. f_equal.
  replace (ao + (24 + 40 * k)) with ((24 + 40 * k) + (ao / 4096) * 4096) by (Z.div_mod_to_equations; nia).
  rewrite Z.mod_add, Z.mod_small by lia. Z.div_mod_to_equations; nia.
Qed.

#[using="Type"] Lemma page_off_mod : forall b o x, b mod 4096 = 0 -> o mod 4096 = 0 -> 0 <= x < 4096 -> (b + o + x) mod 4096 = x.
Proof.
  intros b o x Hb Ho Hx.
  replace (b + o + x) with (x + (b / 4096 + o / 4096) * 4096) by (Z.div_mod_to_equations; nia).
  rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma base16_mod : forall b po, b mod 4096 = 0 -> po mod 16 = 0 -> (b + po) mod 16 = 0.
Proof.
  intros b po Hb Hp. replace (b + po) with ((b / 4096) * 256 * 16 + (po / 16) * 16) by (Z.div_mod_to_equations; lia).
  rewrite <- Z.mul_add_distr_r, Z.mod_mul. reflexivity. lia.
Qed.

(* [comment removed for export] *)
Definition freeW (sp : word) (P G : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.

#[using="Type"] Lemma rd8_known {R} st q v (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma rd16_known {R} st q v0 v1 (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v0 ->
  cell_read (get_shadow st (fst q)) (snd q + 1) = Known v1 ->
  rd16 st q k = k (v0 + 256 * v1).
Proof. intros H0 H1. unfold rd16, rd8. rewrite H0. cbn [fst snd aadd]. rewrite H1. reflexivity. Qed.

#[using="Type"] Lemma get_meta_rec_wr8 st q v g : get_meta_rec (wr8 q v st) g = get_meta_rec st g.
Proof. reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_wr16 st q v g : get_meta_rec (wr16 q v st) g = get_meta_rec st g.
Proof. reflexivity. Qed.

#[using="Type"] Lemma optr_eqb_refl : forall q : aptr, optr_eqb (Some q) (Some q) = true.
Proof. intros [qa qb]. unfold optr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma free_trivial_model : forall st (p : aptr) g gh ar (b3 lo hi : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  let st' := upd_meta g (m_set_freed (m_freed mr + bit idx)) (wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)) in
  let reserved := Z.shiftr b3 5 in
  let e := aadd (slot_start' mr idx) (get_stride mr - IB) in
  po mod 16 = 0 ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
  0 <= m_avail mr -> 0 <= m_freed mr -> 0 <= b3 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  (m_maplen mr <> 0 -> off16 <= m_maplen mr * 4096 / UNIT - 1) ->
  (* [comment removed for export] *)
  reserved < 5 -> reserved <= snd e - po ->
  cell_read sh (snd e - reserved) = Known 0 -> cell_read sh (snd e) = Known 0 ->
  (* [comment removed for export] *)
  m_freed mr <> 0 -> Z.lor (m_freed mr) (m_avail mr) + bit idx <> mask_upto (m_last_idx mr) ->
  free st (Some p) = ret st'.
Proof.
  intros until hi. intros sh po off16 idx base mr st' reserved e AL C4 C3 C2 C1 Hgh Hg Hmem Har Hchk AV FR B3
         Hidx Hav Hfr Hsc Hsc63 Hml RES5 RESe E1 E0 Hfz Hall.
  unfold free, free_hdr, get_meta, guard. fold po. rewrite (proj2 (Z.eqb_eq _ _) AL).
  rewrite (rd16_known st (aadd p (-2)) lo hi) by (cbn [fst snd aadd]; fold po; first [replace (po + -2) with (po - 2) by lia; exact C2 | replace (po + -2 + 1) with (po - 1) by lia; exact C1]).
  cbv beta.
  rewrite (rd8_known st (aadd p (-3)) b3) by (cbn [fst snd aadd]; fold po; replace (po + -3) with (po - 3) by lia; exact C3).
  cbv beta.
  rewrite (rd8_known st (aadd p (-4)) 0) by (cbn [fst snd aadd]; fold po; replace (po + -4) with (po - 4) by lia; exact C4).
  cbv beta. cbn [Z.eqb negb].
  fold off16. fold base. unfold get_group. rewrite Hgh, Hg. fold mr. rewrite Hmem, optr_eqb_refl.
  fold idx. replace (idx <=? m_last_idx mr) with true by (symmetry; apply Z.leb_le; lia).
  unfold testbit. rewrite Hav, Hfr. cbn [negb].
  rewrite Har, Hchk, Z.eqb_refl.
  match goal with |- context [if (if ?c then ?x else ?y) then _ else SVis (EUndef (UAssert 16)) _] =>
    replace (if c then x else y) with true end.
  2:{ destruct (Z.ltb_spec (m_sizeclass mr) 48).
      - specialize (Hsc ltac:(lia)). symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
      - specialize (Hsc63 ltac:(lia)). symmetry. apply Z.eqb_eq. lia. }
  match goal with |- context [if (if ?c then ?x else ?y) then _ else SVis (EUndef (UAssert 17)) _] =>
    replace (if c then x else y) with true end.
  2:{ destruct (Z.eqb_spec (m_maplen mr) 0); cbn [negb]; [reflexivity|]. symmetry. apply Z.leb_le. apply Hml. assumption. }
  unfold slot_start. rewrite Hmem.
  assert (He : aadd (aadd base (UNIT + get_stride mr * idx)) (get_stride mr - IB) = e) by (unfold e, slot_start'; rewrite Hmem; reflexivity).
  rewrite He.
  assert (Fe : fst e = fst p) by (rewrite <- He; reflexivity).
  unfold get_nominal_size.
  rewrite (rd8_known st (aadd p (-3)) b3) by (cbn [fst snd aadd]; fold po; replace (po + -3) with (po - 3) by lia; exact C3).
  cbv beta. fold reserved.
  replace (5 <=? reserved) with false by (symmetry; apply Z.leb_gt; lia).
  fold po. replace (reserved <=? snd e - po) with true by (symmetry; apply Z.leb_le; lia).
  rewrite (rd8_known st (aadd e (- reserved)) 0) by (cbn [fst snd aadd]; rewrite Fe; fold sh; replace (snd e + - reserved) with (snd e - reserved) by lia; exact E1).
  cbv beta. cbn [Z.eqb].
  rewrite (rd8_known st e 0) by (rewrite Fe; exact E0).
  unfold guard. cbn [Z.eqb]. unfold Malloc.ret at 1. rewrite sbind_ret_l.
  unfold free_tail, guard. rewrite !get_meta_rec_wr16, !get_meta_rec_wr8. fold mr.
  unfold testbit. rewrite Z.lor_spec, Hfr, Hav. cbn [orb negb].
  replace (m_freed mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hfz).
  replace (Z.lor (m_freed mr) (m_avail mr) + bit idx =? mask_upto (m_last_idx mr)) with false by (symmetry; apply Z.eqb_neq; exact Hall).
  cbn [orb negb]. reflexivity.
Qed.

End PORT.

End WithCeil.
End F_malloc_free.

(* [comment removed for export] *)
Module F_malloc_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma swrap_word x : Z_to_bv 64 (bv_swrap 32 x) = wz (sxv x).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

#[using="Type"] Lemma sxv_testbit_lo' v i : 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
  intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. apply Z.mod_pow2_bits_low. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sxv_cases' v : let u := v mod 2^32 in
  (u < 2^31 /\ sxv v = u) \/ (2^31 <= u /\ sxv v = u + 2^64 - 2^32).
Proof.
  cbv zeta. pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
  rewrite <- (sxv_congr (v mod 2^32) v) by (apply Z.mod_mod; lia).
  destruct (sxv_cases (v mod 2^32) ltac:(lia)); tauto.
Qed.

#[using="Type"] Lemma testbit_31_mod32 v : Z.testbit v 31 = (2^31 <=? v mod 2^32).
Proof.
  rewrite <- (Z.mod_pow2_bits_low v 32 31) by lia. rewrite Z.testbit_eqb by lia.
  pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
  destruct (Z.leb_spec (2^31) (v mod 2^32)).
  - replace (v mod 2^32 / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
  - rewrite Z.div_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma sxv_testbit_hi v i : 31 <= i < 64 -> Z.testbit (sxv v) i = Z.testbit v 31.
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

#[using="Type"] Lemma sxv_testbit_high v i : 64 <= i -> Z.testbit (sxv v) i = false.
Proof.
  intros. pose proof (sxv_range v). destruct (Z.eq_dec (sxv v) 0) as [->|]. apply Z.bits_0.
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed.

#[using="Type"] Lemma sxv_land a b : Z.land (sxv a) (sxv b) = sxv (Z.land a b).
Proof.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 32); [| destruct (Z.lt_ge_cases i 64)].
  - rewrite !sxv_testbit_lo' by lia. symmetry. apply Z.land_spec.
  - rewrite !sxv_testbit_hi by lia. rewrite Z.land_spec. reflexivity.
  - rewrite !sxv_testbit_high by lia. reflexivity.
Qed.

#[using="Type"] Lemma sxv_idem v : sxv (sxv v) = sxv v.
Proof. apply sxv_congr. apply sxv_mod32. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_opp_odd a : Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

#[using="Type"] Lemma land_opp_even a : Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (- a).
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite !Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

#[using="Type"] Lemma lowbit_pow2 : forall m, 0 < m -> exists k, 0 <= k /\ Z.land m (- m) = 2 ^ k /\ 2 ^ k <= m.
Proof.
  intros m Hm.
  pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
  cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
  intros x IH Hx0 Hx.
  destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
  - destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
    exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
  - exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.

#[using="Type"] Lemma land_opp_pow2 k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
  intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
  subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma lowbit_nonzero m : 0 < m -> exists k, 0 <= k /\ lowbit m = 2 ^ k /\ 2 ^ k <= m.
Proof. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.

#[using="Type"] Lemma lowbit_0 : lowbit 0 = 0.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ctz32_pow2 k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma negw_and_lowbit v : 0 <= v < 2^32 ->
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
Definition DB32 : Z := 124511785.   (* [comment removed for export] *)
Definition dbi (k : Z) : Z := ((2 ^ k * DB32) mod 2^32) / 2^27.

#[using="Type"] Lemma lowbit_pow2_id k : 0 <= k -> lowbit (2 ^ k) = 2 ^ k.
Proof. intros. unfold lowbit. apply land_opp_pow2. assumption. Qed.

#[using="Type"] Lemma mulw_word a c : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv a)) * c)) = wz (sxv (a * c)).
Proof.
  rewrite wz_unsigned by apply sxv_range. rewrite swrap_word. unfold wz. f_equal. apply sxv_congr.
  rewrite <- Z.mul_mod_idemp_l, sxv_mod32, Z.mul_mod_idemp_l by lia. reflexivity.
Qed.

#[using="Type"] Lemma srliw27_val a : bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (wz (sxv a)))) 27) = (a mod 2^32) / 2^27.
Proof.
  rewrite wz_unsigned by apply sxv_range.
  change (bv_wrap 32 (sxv a)) with ((sxv a) mod 2^32). rewrite sxv_mod32.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)).
  apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

#[using="Type"] Lemma dbi_range k : 0 <= dbi k < 32.
Proof. unfold dbi. pose proof (Z.mod_pos_bound (2^k * DB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma le4_avail_sub a b : 0 <= b <= a -> a < 2^32 ->
  le4 (wz (sxv (sxv a - sxv b))) = le4 (wz (a - b)).
Proof.
  intros. apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
  rewrite sxv_mod32, <- Zminus_mod_idemp_r, sxv_mod32, <- Zminus_mod_idemp_l, sxv_mod32, Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  reflexivity.
Qed.

#[using="Type"] Lemma srliw27_word a :
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (wz (sxv a)))) 27)) = wz ((a mod 2^32) / 2^27).
Proof. rewrite srliw27_val. reflexivity. Qed.

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

(* [comment removed for export] *)
#[using="Type"] Lemma rw_cells_CB_len segs m A n bs rest : rw_cells segs m A (CB n bs :: rest) -> length bs = n.
Proof. intros [[[H _] _] _]. exact H. Qed.

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

End PORT.

End WithCeil.
End F_malloc_fast.

(* [comment removed for export] *)
Module F_malloc_enframe.
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Definition smear (s : Z) : Z :=
  let m1 := Z.lor s (Z.shiftr s 1) in
  let m2 := Z.lor m1 (Z.shiftr m1 2) in
  Z.lor m2 (Z.shiftr m2 4).

#[using="Type"] Lemma fold_off_eq off slack :
  fold_off off slack =
  (if slack <? off then
     let x := Z.land off (smear slack) in if slack <? x then x - (slack + 1) else x
   else off).
Proof. reflexivity. Qed.

#[using="Type"] Lemma smear_nonneg s : 0 <= s -> 0 <= smear s.
Proof.
  intros. unfold smear.
  repeat (apply Z.lor_nonneg; split); repeat apply Z.shiftr_nonneg; repeat (apply Z.lor_nonneg; split);
    repeat apply Z.shiftr_nonneg; try lia; repeat (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
  all: try (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
Qed.

#[using="Type"] Lemma land_le_l a b : 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros. rewrite <- (Z.lor_ldiff_and a b) at 2.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia).
  assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia).
  assert (Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by assumption. lia.
Qed.

(* [comment removed for export] *)
Definition zseq (a n : Z) : list Z := map Z.of_nat (seq (Z.to_nat a) (Z.to_nat n)).

(* [comment removed for export] *)
Definition fold_fn1 (s off : Z) : bool :=
  let x := Z.land off (smear s) in (negb (s <? x)) || (x - (s + 1) <=? s).
Definition fold_fn (s : Z) : bool := forallb (fold_fn1 s) (zseq 0 256).
Definition fold_check : bool := forallb fold_fn (zseq 0 128).

#[using="Type"] Lemma fold_check_true : forallb fold_fn (zseq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma forallb_zseq (f : Z -> bool) a n x : forallb f (zseq a n) = true -> 0 <= a -> a <= x < a + n -> f x = true.
Proof.
  intros H Ha Hx. unfold zseq in H. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

#[using="Type"] Lemma fold_assert_ok off slack : 0 <= off < 256 -> 0 <= slack ->
  slack < Z.land off (smear slack) -> Z.land off (smear slack) - (slack + 1) <= slack.
Proof.
  intros Ho Hs Hlt.
  pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  destruct (Z.lt_ge_cases slack 128).
  - pose proof (forallb_zseq fold_fn 0 128 slack fold_check_true ltac:(lia) ltac:(lia)) as H1. unfold fold_fn in H1.
    pose proof (forallb_zseq (fold_fn1 slack) 0 256 off H1 ltac:(lia) ltac:(lia)) as H2. unfold fold_fn1 in H2. cbv zeta in H2.
    apply orb_prop in H2. destruct H2 as [H2|H2].
    + apply negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
    + apply Z.leb_le in H2. exact H2.
  - lia.
Qed.

#[using="Type"] Lemma fold_off_range off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= Z.max slack off /\ fold_off off slack < 256.
Proof.
  intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
  destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
  destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
  pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma fold_off_le_slack off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= slack.
Proof.
  intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
  destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
  destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
  pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma land_126 y : Z.land y 126 = 2 * Z.land (Z.shiftr y 1) 63.
Proof.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|].
  - rewrite Z.testbit_even_0. change 126 with (2 * 63). rewrite Z.testbit_even_0. apply andb_false_r.
  - replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ by lia.
    change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
    replace (i - 1 + 1) with i by lia. replace (Z.succ (i - 1)) with i by lia. reflexivity.
Qed.

#[using="Type"] Lemma mword_sc last_idx freeable sc maplen :
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen ->
  Z.land (Z.shiftr (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) 5) 126 = 2 * sc.
Proof.
  intros. rewrite land_126. rewrite Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. change (2 ^ (5 + 1)) with 64.
  change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2^6) with 64.
  replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) / 64) with (sc + 64 * maplen) by (Z.div_mod_to_equations; lia).
  replace ((sc + 64 * maplen) mod 64) with sc by (Z.div_mod_to_equations; lia). reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac sdk :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (try lazymatch goal with
     | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
     end);
    transport_chunks segs m E bs;
    repeat match goal with
    | STq : stk segs m ?loq ?hiq |- _ =>
        first [ apply (stk_write segs m loq hiq E bs) in STq; [ | lia | simpl_sizes; slia ]
              | fail 100 "sdk: cannot transport stk hypothesis" STq ]
    | MU : munch ?Wq ?mq m |- _ =>
        first [ apply (munch_write Wq mq m E bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
              | fail 100 "sdk: store outside the declared footprint" ]
    | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa E) bs) in WMo
    end;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    let m' := fresh "m" in let Eq := fresh "EQ" m' in
    remember (write_to_mem m (wa E) bs) as m' eqn:Eq
  end.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma le1_wz v : 0 <= v < 256 -> le1 (wz v) = [b8 v].
Proof. intros. cbn. rewrite (wz_unsigned v) by lia. reflexivity. Qed.

#[using="Type"] Lemma le1_neg32 : le1 (Z_to_bv 64 (-32)) = [b8 224].
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition enframe_tail_mem (m : word -> option byte) (P E n k q : Z) : word -> option byte :=
  let m1 := write_to_mem m (wa (P - 2)) (le2 (wz q)) in
  let m2 := write_to_mem m1 (wa (P - 3)) [b8 k] in
  let r := E - P - n in
  let m3 := if r =? 0 then m2 else write_to_mem m2 (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 4)) (le4 (wz r))) (wa (E - 5)) [b8 0], 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

Definition enframe_off_mem (m : word -> option byte) (P0 off : Z) : word -> option byte :=
  if off =? 0 then m
  else write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 2)) (le2 (wz off))) (wa (P0 - 3)) [b8 224])
                    (wa (P0 + 16 * off - 4)) [b8 0].

(* [comment removed for export] *)
Section FASTMODEL.
Context {O : Type}.
Variable pans : O -> aptr -> Z -> Z -> Z.
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Let pupd : O -> ev -> Z -> O := fun o _ _ => o.
Local Notation prun := (prun pans pupd).

(* [comment removed for export] *)
Definition rdv (o : O) (st : mstate) (q : aptr) : Z :=
  match cell_read (get_shadow st (fst q)) (snd q) with
  | Known v => v
  | Unknown h => pans o q (conc st q) h
  end.

#[using="Hpans"] Lemma rd8_oracle {R} o st q (k : Z -> M R) : prun o (rd8 st q k) = prun o (k (rdv o st q)).
Proof.
  unfold rd8, rdv. destruct (cell_read _ _) as [v|h]; [reflexivity|].
  unfold MallocCtrl.prun. cbn [eruns psel].
  pose proof (Hpans o q (conc st q) h).
  replace (peek_answer_ok (pans o q (conc st q) h)) with true.
  2:{ symmetry. unfold peek_answer_ok. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  reflexivity.
Qed.

#[using="Hpans"] Lemma rd16_oracle {R} o st q (k : Z -> M R) :
  prun o (rd16 st q k) = prun o (k (rdv o st q + 256 * rdv o st (aadd q 1))).
Proof. unfold rd16. rewrite rd8_oracle, rd8_oracle. reflexivity. Qed.

#[using="Type"] Lemma land_opp_pow2' k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
  intros Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k i); cbn [andb]; [|reflexivity].
  subst. replace (i <? i) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? i); reflexivity.
Qed.
#[using="Type"] Lemma ctz32_pow2' k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2' by lia. apply Z.log2_pow2. lia. Qed.

#[using="Type"] Lemma get_meta_rec_upd_same st g f : get_meta_rec (upd_meta g f st) g = f (get_meta_rec st g).
Proof. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn. rewrite lookup_insert_eq. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma malloc_core_fast st n g k :
  let sc := size_to_class n in
  let mr := get_meta_rec st g in
  size_overflows n = false -> n < MMAP_THRESHOLD ->
  active st sc = Some g -> 0 < m_avail mr -> 0 <= k -> lowbit (m_avail mr) = 2 ^ k ->
  malloc_core full_lay st n = ret (upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st, Some (g, k)).
Proof.
  intros sc mr OV TH ACT AV K0 LB.
  unfold malloc_core. rewrite OV. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
  unfold malloc_small_ctrl. fold sc. rewrite ACT. rewrite ACT. fold mr. rewrite LB.
  assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  replace (2 ^ k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite ctz32_pow2' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hpans"] Lemma malloc_fast_model o st n g k :
  let sc := size_to_class n in
  let st1 := set_tick (N.succ (s_tick st)) st in
  let mr := get_meta_rec st1 g in
  let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1 in
  let stride := get_stride mr in
  let slack := (stride - IB - n) / UNIT in
  let p0 := slot_start' mr k in
  let ctr := c_mmap_counter (ctx st) in
  let b3 := rdv o st2 (aadd p0 (-3)) in
  let v16 := rdv o st2 (aadd p0 (-2)) + 256 * rdv o st2 (aadd (aadd p0 (-2)) 1) in
  let off0 := (if b3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255) in
  let off := fold_off off0 slack in
  size_overflows n = false -> n < MMAP_THRESHOLD ->
  active st sc = Some g -> 0 < m_avail mr -> 0 <= k -> lowbit (m_avail mr) = 2 ^ k ->
  prun o (malloc st n) = SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)),
                                   Some (snd (enframe_at st2 g k n off)))).
Proof.
  intros sc st1 mr st2 stride slack p0 ctr b3 v16 off0 off OV TH ACT AV K0 LB.
  unfold malloc. fold st1.
  rewrite (malloc_core_fast st1 n g k OV TH ACT AV K0 LB). unfold Malloc.ret. rewrite sbind_ret_l.
  unfold enframe_full, enframe_read_off. fold st2. rewrite (get_meta_rec_upd_same st1 g). fold mr.
  set (K := fun off' : Z => let '(st3, p) := enframe_at st2 g k n off' in @SRet ev Z _ (havoc p n st3, Some p)).
  change (prun o (rd8 st2 (aadd p0 (-3)) (fun b => if negb (b =? 0)
             then rd16 st2 (aadd p0 (-2)) (fun o16 => K (fold_off (Z.land (o16 + 1) 255) slack))
             else K (fold_off (Z.land ctr 255) slack)))
          = SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)), Some (snd (enframe_at st2 g k n off))))).
  rewrite rd8_oracle. cbv beta. fold b3.
  assert (FIN : forall off', off' = off -> prun o (K off') = SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)), Some (snd (enframe_at st2 g k n off))))).
  { intros off' ->. unfold K. destruct (enframe_at st2 g k n off) as [st3 p]. reflexivity. }
  destruct (Z.eqb_spec b3 0) as [E|NE]; cbn [negb].
  - apply FIN. unfold off, off0. replace (b3 =? 0) with true by (symmetry; apply Z.eqb_eq; exact E). reflexivity.
  - rewrite rd16_oracle. cbv beta. apply FIN. unfold off, off0. replace (b3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
Qed.
End FASTMODEL.

End PORT.

End WithCeil.
End F_malloc_enframe.

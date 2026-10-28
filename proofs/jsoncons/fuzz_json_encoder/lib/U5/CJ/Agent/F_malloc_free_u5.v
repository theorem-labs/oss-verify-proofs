(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_syscalls_u5 MallocRep_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

(* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sxv (v : Z) : Z := (bv_swrap 32 v) mod 2^64.

Lemma sxv_range v : 0 <= sxv v < 2^64.
Proof. unfold sxv. apply Z.mod_pos_bound. lia. Qed.

Lemma swrap32_eq' z : bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.
End CEIL_WRAP_1.


Ltac pow_lits :=
  change (2^64)%Z with 18446744073709551616%Z in *;
  change (2^63)%Z with 9223372036854775808%Z in *;
  change (2^33)%Z with 8589934592%Z in *;
  change (2^32)%Z with 4294967296%Z in *;
  change (2^31)%Z with 2147483648%Z in *.
Ltac mlia := pow_lits; Z.div_mod_to_equations; lia.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.


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
Lemma self_word b3 : 0 <= b3 < 256 ->
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

Lemma wz_inj a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> wz a = wz b -> a = b.
Proof. intros Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !wz_unsigned in E by lia. exact E. Qed.

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

Lemma self_word' b3 : 0 <= b3 < 256 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 (Z.land b3 31)) mod 32)))
  = wz (sxv (2 ^ (Z.land b3 31))).
Proof.
  intros.
  assert (0 <= Z.land b3 31 < 32).
  { split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite (wz_unsigned (Z.land b3 31)) by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

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
End CEIL_WRAP_2.


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
Section CEIL_WRAP_3.
Context {RUNp : RunP}.


Definition frozen (P : Prop) : Prop := P.

Definition free_W (sp : word) (P G : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.

Definition free_triv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : word -> option byte) (P G v : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (free_W sp P G) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m2 /\ wmono asegs m m2
    /\ m' = write_to_mem (write_to_mem (write_to_mem m2 (wa (P - 3)) [b8 255]) (wa (P - 2)) (le2 (wz 0)))
                         (wa (G + 28)) (le4 (wz v)).
End CEIL_WRAP_3.

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
Section CEIL_WRAP_4.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wr_at_sub : forall segs m A n A' n',
  wr_at segs m A n -> A <= A' -> A' + n' <= A + n -> wr_at segs m A' n'.
Proof.
  intros segs m A n A' n' (H0 & H1 & H) LA LB. split; [lia|]. split; [lia|].
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
Definition freeW (sp : word) (P G : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rd8_known {R} st q v (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.

Lemma rd16_known {R} st q v0 v1 (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v0 ->
  cell_read (get_shadow st (fst q)) (snd q + 1) = Known v1 ->
  rd16 st q k = k (v0 + 256 * v1).
Proof. intros H0 H1. unfold rd16, rd8. rewrite H0. cbn [fst snd aadd]. rewrite H1. reflexivity. Qed.

Lemma get_meta_rec_wr8 st q v g : get_meta_rec (wr8 q v st) g = get_meta_rec st g.
Proof. reflexivity. Qed.
Lemma get_meta_rec_wr16 st q v g : get_meta_rec (wr16 q v st) g = get_meta_rec st g.
Proof. reflexivity. Qed.

Lemma optr_eqb_refl : forall q : aptr, optr_eqb (Some q) (Some q) = true.
Proof. intros [qa qb]. unfold optr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma free_trivial_model : forall st (p : aptr) g gh ar (b3 lo hi : Z),
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
End CEIL_WRAP_4.


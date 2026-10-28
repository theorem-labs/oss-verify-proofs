(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Arr Walk Mem Frame Cells Step.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_unwind_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma Z_to_le_bytes_inv : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  assert (Hnn : 0 <= bytes_le_to_Z bs).
  { clear. induction bs as [|c bs IH]; cbn [bytes_le_to_Z]; [lia|].
    apply Z.lor_nonneg. split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; exact IH]. }
  assert (E : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8) = bv_unsigned b + 256 * bytes_le_to_Z bs).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
    rewrite <- Z.lxor_lor.
    - rewrite <- Z.add_nocarry_lxor; [lia|].
      apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.lt_ge_cases i 8) as [L|G].
      + replace (bytes_le_to_Z bs * 256) with (bytes_le_to_Z bs * 2 ^ 8) by lia. rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
      + rewrite (Z.bits_above_log2 (bv_unsigned b) i); [reflexivity| lia|].
        destruct (Z.eq_dec (bv_unsigned b) 0) as [->|N]; [cbn; lia|].
        apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (2 ^ 8); [change (2 ^ 8) with 256; lia| apply Z.pow_le_mono_r; lia].
    - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.lt_ge_cases i 8) as [L|G].
      + replace (bytes_le_to_Z bs * 256) with (bytes_le_to_Z bs * 2 ^ 8) by lia. rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
      + rewrite (Z.bits_above_log2 (bv_unsigned b) i); [reflexivity| lia|].
        destruct (Z.eq_dec (bv_unsigned b) 0) as [->|N]; [cbn; lia|].
        apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (2 ^ 8); [change (2 ^ 8) with 256; lia| apply Z.pow_le_mono_r; lia]. }
  rewrite E. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite (Z.mul_comm 256), Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
    rewrite (Z.mul_comm 256), Z.div_add by lia. rewrite (Z.div_small (bv_unsigned b) 256) by lia. lia.
Qed.

Lemma bytes_le_to_Z_range : forall bs : list byte, 0 <= bytes_le_to_Z bs < 256 ^ Z.of_nat (length bs).
Proof.
  induction bs as [|b bs IH]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  cbn [bytes_le_to_Z length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  assert (E : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8) <= bv_unsigned b + 256 * bytes_le_to_Z bs).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
    pose proof (Z.add_lor_land (bv_unsigned b) (bytes_le_to_Z bs * 256)) as AL.
    assert (0 <= Z.land (bv_unsigned b) (bytes_le_to_Z bs * 256)) by (apply Z.land_nonneg; left; lia). lia. }
  split; [apply Z.lor_nonneg; split; [lia| apply Z.shiftl_nonneg; lia]| nia].
Qed.

Lemma le8_surj : forall bs : list byte, length bs = 8%nat -> exists w : word, le8 w = bs.
Proof.
  intros bs Hl. exists (Z_to_bv 64 (bytes_le_to_Z bs)). unfold le8, word_to_le_bytes.
  pose proof (bytes_le_to_Z_range bs) as R. rewrite Hl in R. change (256 ^ Z.of_nat 8) with (2 ^ 64) in R.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact R.
  rewrite <- Hl at 1. apply Z_to_le_bytes_inv.
Qed.

Lemma stk_rec16 : forall (m : mem) a, stk bsegs m a (a + 16) -> exists fp ra : word, rw_cells bsegs m a [C8 fp; C8 ra].
Proof.
  intros m a ST.
  destruct (stk_carve bsegs m a (a + 16) 16 ST ltac:(lia)) as [_ (junk & FR)].
  replace (a + 16 - Z.of_nat 16) with a in FR by lia.
  destruct FR as [[WF BA] WR]. cbn [cells_wf cell_wf] in WF. destruct WF as [HL _].
  cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
  destruct (le8_surj (firstn 8 junk)) as (w1 & E1); [rewrite firstn_length; lia|].
  destruct (le8_surj (skipn 8 junk)) as (w2 & E2); [rewrite skipn_length; lia|].
  exists w1, w2. split; [split|].
  - cbn. exact (conj I (conj I I)).
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, E1, E2, firstn_skipn. exact BA.
  - cbn [cells_size csize] in *. exact WR.
Qed.

Definition rng64w (x : Z) : Prop := 0 <= x < 2 ^ 64.

Lemma uw_loop_gen : forall (m : mem) pc page hi maxd wlo (k : nat) f acc,
  stk bsegs m wlo hi -> 0 <= wlo -> hi <= 2 ^ 64 ->
  wlo + 16 <= f -> f < hi -> hi - f <= Z.of_nat k -> Forall rng64w acc ->
  exists ch tr, chain_cells [(0, wlo)] m f ch /\ uw_loop pc page hi maxd ch f acc = Some tr /\ Forall rng64w tr.
Proof.
  intros m pc page hi maxd wlo k. induction k as [|k IH]; intros f acc ST W0 H64 Hf1 Hf2 Hk HA; [lia|].
  destruct (stk_split bsegs m wlo (f - 16) hi ST ltac:(lia)) as [_ S2].
  destruct (stk_split bsegs m (f - 16) f hi S2 ltac:(lia)) as [S3 _].
  replace f with (f - 16 + 16) in S3 at 2 by lia.
  destruct (stk_rec16 m (f - 16) S3) as (fpw & raw & RC).
  set (fp := bv_unsigned fpw). set (ra := bv_unsigned raw).
  assert (Rfp : 0 <= fp < 2 ^ 64) by (apply bv_unsigned_in_range).
  assert (Rra : 0 <= ra < 2 ^ 64) by (apply bv_unsigned_in_range).
  assert (CELL : rw_cells bsegs m (f + -16) [C8 (Z_to_bv 64 fp); C8 (Z_to_bv 64 ra)]).
  { unfold fp, ra. rewrite !Z_to_bv_bv_unsigned. replace (f + -16) with (f - 16) by lia. exact RC. }
  assert (DJ : disjoint_from [(0, wlo)] (f + -16) 16) by (cbn [disjoint_from]; split; [lia| exact I]).
  assert (HA' : Forall rng64w (if ra =? pc then acc else acc ++ [ra])).
  { destruct (ra =? pc); [exact HA|]. apply Forall_app. split; [exact HA|]. constructor; [exact Rra| constructor]. }
  destruct (fr_ok f hi fp) eqn:FO.
  -
    assert (FO' := FO). unfold fr_ok in FO'. apply andb_prop in FO'. destruct FO' as [FO' _]. apply andb_prop in FO'. destruct FO' as [L1 L2].
    apply Z.ltb_lt in L1. apply Z.ltb_lt in L2.
    destruct (IH fp (if ra =? pc then acc else acc ++ [ra]) ST W0 H64 ltac:(lia) L2 ltac:(lia) HA') as (ch' & tr' & CC' & UL' & TR').
    exists ((ra, fp) :: ch').
    cbn [uw_loop chain_cells].
    destruct (maxd <=? Z.of_nat (length acc)); [exists acc; split; [split; [exact CELL| split; [lia| split; [exact DJ| exact CC']]]| split; [reflexivity| exact HA]]|].
    destruct (ra <? page); [exists acc; split; [split; [exact CELL| split; [lia| split; [exact DJ| exact CC']]]| split; [reflexivity| exact HA]]|].
    rewrite FO. exists tr'. split; [split; [exact CELL| split; [lia| split; [exact DJ| exact CC']]]| split; [exact UL'| exact TR']].
  - exists [(ra, fp)]. cbn [uw_loop chain_cells].
    destruct (maxd <=? Z.of_nat (length acc)); [exists acc; split; [split; [exact CELL| split; [lia| split; [exact DJ| exact I]]]| split; [reflexivity| exact HA]]|].
    destruct (ra <? page); [exists acc; split; [split; [exact CELL| split; [lia| split; [exact DJ| exact I]]]| split; [reflexivity| exact HA]]|].
    rewrite FO. eexists. split; [split; [exact CELL| split; [lia| split; [exact DJ| exact I]]]| split; [reflexivity| exact HA']].
Qed.

Definition unwind_gen_ok (s0 sp : Z) : Prop := s0 <= sp \/ s0 mod 8 <> 0 \/ sp + 16 <= s0.

Lemma gen_trace_main : forall (m : mem) pc bot top maxd wlo usp hi' ra s0,
  stk bsegs m wlo hi' -> 0 <= wlo -> wlo <= usp -> hi' <= 2 ^ 64 -> top - 16 <= hi' -> 1 <= maxd ->
  rng64w pc -> rng64w ra -> unwind_gen_ok s0 usp ->
  exists ch tr, chain_cells [(0, usp)] m s0 ch
    /\ unwind_trace pc 4096 bot top maxd usp ((ra, s0) :: ch) = Some tr
    /\ (1 <= Z.of_nat (length tr) <= maxd) /\ Forall rng64w tr.
Proof.
  intros m pc bot top maxd wlo usp hi' ra s0 ST W0 WU H64 HT HM Rpc Rra UG.
  assert (HP : Forall rng64w [pc]) by (constructor; [exact Rpc| constructor]).
  assert (KEY : exists ch tr, chain_cells [(0, usp)] m s0 ch /\ unwind_trace pc 4096 bot top maxd usp ((ra, s0) :: ch) = Some tr /\ Forall rng64w tr).
  { unfold unwind_trace.
    destruct (top / 4096 =? 0); [exists [], [pc]; split; [exact I| split; [reflexivity| exact HP]]|].
    destruct (fr_ok bot (top - 16) usp); [| exists [], [pc]; split; [exact I| split; [reflexivity| exact HP]]].
    cbn [uw_loop length].
    destruct (maxd <=? Z.of_nat 1); [exists [], [pc]; split; [exact I| split; [reflexivity| exact HP]]|].
    destruct (ra <? 4096); [exists [], [pc]; split; [exact I| split; [reflexivity| exact HP]]|].
    assert (HA' : Forall rng64w (if ra =? pc then [pc] else [pc] ++ [ra])).
    { destruct (ra =? pc); [exact HP|]. constructor; [exact Rpc|]. constructor; [exact Rra| constructor]. }
    destruct (fr_ok usp (top - 16) s0) eqn:FO.
    - assert (FO' := FO). unfold fr_ok in FO'. apply andb_prop in FO'. destruct FO' as [FO' A8]. apply andb_prop in FO'. destruct FO' as [L1 L2].
      apply Z.ltb_lt in L1. apply Z.ltb_lt in L2. apply Z.eqb_eq in A8.
      assert (S16 : usp + 16 <= s0) by (destruct UG as [UG|[UG|UG]]; [lia| contradiction| exact UG]).
      destruct (stk_split bsegs m wlo usp hi' ST ltac:(lia)) as [_ ST1].
      destruct (stk_split bsegs m usp (top - 16) hi' ST1 ltac:(lia)) as [ST' _].
      destruct (uw_loop_gen m pc 4096 (top - 16) maxd usp (Z.to_nat (top - 16 - s0)) s0 (if ra =? pc then [pc] else [pc] ++ [ra])
                  ST' ltac:(lia) ltac:(lia) S16 L2 ltac:(lia) HA') as (ch & tr & CC & UL & TR).
      exists ch, tr. split; [exact CC| split; [exact UL| exact TR]].
    - exists []. eexists. split; [exact I| split; [reflexivity| exact HA']]. }
  destruct KEY as (ch & tr & CC & UT & TR). exists ch, tr. split; [exact CC|]. split; [exact UT|]. split; [| exact TR].
  exact (unwind_trace_length _ _ _ _ _ _ _ _ UT HM).
Qed.

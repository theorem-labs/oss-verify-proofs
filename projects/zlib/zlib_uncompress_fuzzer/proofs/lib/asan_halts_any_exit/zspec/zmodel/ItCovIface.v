(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import Prog ZIface InflateState Inftrees ModelRel InftreesCoverage.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ItCovBits ItCovPre ItCovMath ItCovStep ItCovLoop ItCovMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma w8_range : forall z, 0 <= wrap8 z < 256.
Proof. intros z. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma w16_range : forall z, 0 <= wrap16 z < 65536.
Proof. intros z. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma w8_small : forall z, 0 <= z < 256 -> wrap8 z = z.
Proof. intros z Hz. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma w16_small : forall z, 0 <= z < 65536 -> wrap16 z = z.
Proof. intros z Hz. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma code_op_pack : forall op bits val, code_op (code_pack op bits val) = wrap8 op.
Proof.
  intros op bits val. unfold code_op, code_pack. pose proof (w8_range op). pose proof (w8_range bits). pose proof (w16_range val).
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  replace (wrap8 op + 256 * wrap8 bits + 65536 * wrap16 val) with (wrap8 op + (wrap8 bits + 256 * wrap16 val) * 256) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma code_bits_pack : forall op bits val, InflateState.code_bits (code_pack op bits val) = wrap8 bits.
Proof.
  intros op bits val. unfold InflateState.code_bits, code_pack. pose proof (w8_range op). pose proof (w8_range bits). pose proof (w16_range val).
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace (wrap8 op + 256 * wrap8 bits + 65536 * wrap16 val) with (wrap8 op + (wrap8 bits + 256 * wrap16 val) * 256) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small (wrap8 op) 256) by lia. rewrite Z.add_0_l.
  replace (wrap8 bits + 256 * wrap16 val) with (wrap8 bits + wrap16 val * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma code_val_pack : forall op bits val, code_val (code_pack op bits val) = wrap16 val.
Proof.
  intros op bits val. unfold code_val, code_pack. pose proof (w8_range op). pose proof (w8_range bits). pose proof (w16_range val).
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
  replace (wrap8 op + 256 * wrap8 bits + 65536 * wrap16 val) with ((wrap8 op + 256 * wrap8 bits) + wrap16 val * 65536) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small (wrap8 op + 256 * wrap8 bits) 65536) by lia. rewrite Z.add_0_l.
  apply Z.mod_small. lia.
Qed.


Lemma ent_CODES : forall w, 0 <= w <= 18 -> ent_op CODES w = 0 /\ ent_val CODES w = w.
Proof.
  intros w Hw. unfold ent_op, ent_val. cbn [it_match].
  replace (w + 1 <? 20) with true by (symmetry; apply Z.ltb_lt; lia). split; reflexivity.
Qed.

Lemma ent_LENS_lit : forall w, 0 <= w < 256 -> ent_op LENS w = 0 /\ ent_val LENS w = w.
Proof.
  intros w Hw. unfold ent_op, ent_val. cbn [it_match].
  replace (w + 1 <? 257) with true by (symmetry; apply Z.ltb_lt; lia). split; reflexivity.
Qed.
Lemma ent_LENS_eob : ent_op LENS 256 = 96 /\ ent_val LENS 256 = 0.
Proof. split; reflexivity. Qed.
Lemma ent_LENS_len : forall w, 257 <= w ->
  ent_op LENS w = wrap8 (arr_get lext_a (w - 257)) /\ ent_val LENS w = arr_get lbase_a (w - 257).
Proof.
  intros w Hw. unfold ent_op, ent_val. cbn [it_match].
  replace (w + 1 <? 257) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (257 <=? w) with true by (symmetry; apply Z.leb_le; lia). split; reflexivity.
Qed.

Lemma ent_LENS_L : forall w, 0 <= w < 288 ->
  let op := ent_op LENS w in let val := ent_val LENS w in
  (op = 0 /\ val = w /\ w < 256) \/ (op = 96 /\ val = 0) \/ (op = 71 \/ op = 77)
  \/ (16 <= op <= 21 /\ 3 <= val /\ val + 2 ^ (Z.land op 15) - 1 <= 258).
Proof.
  intros w Hw. cbv zeta.
  destruct (Z_lt_le_dec w 256) as [L|L]; [left; destruct (ent_LENS_lit w ltac:(lia)) as [-> ->]; lia|].
  destruct (Z.eq_dec w 256) as [->|NE]; [right; left; exact ent_LENS_eob|].
  destruct (ent_LENS_len w ltac:(lia)) as [-> ->].
  assert (E : exists k, w = 257 + Z.of_nat k /\ (k < 31)%nat) by (exists (Z.to_nat (w - 257)); split; lia).
  destruct E as (k & -> & Hk).
  replace (257 + Z.of_nat k - 257) with (Z.of_nat k) by lia.
  do 31 (destruct k as [|k];
    [ match goal with |- context [arr_get lext_a ?i] =>
        let v := eval vm_compute in (arr_get lext_a i) in replace (arr_get lext_a i) with v by (vm_compute; reflexivity) end;
      match goal with |- context [arr_get lbase_a ?i] =>
        let v := eval vm_compute in (arr_get lbase_a i) in replace (arr_get lbase_a i) with v by (vm_compute; reflexivity) end;
      rewrite w8_small by lia;
      match goal with |- context [2 ^ ?e] => let v := eval vm_compute in (2 ^ e) in change (2 ^ e) with v end;
      lia |]). lia.
Qed.

Lemma ent_DISTS : forall w, 0 <= w < 32 ->
  let op := ent_op DISTS w in let val := ent_val DISTS w in
  op = wrap8 (arr_get dext_a w) /\ val = arr_get dbase_a w
  /\ ((16 <= op <= 29 /\ 1 <= val <= 24577) \/ (op = 64 /\ 30 <= w)).
Proof.
  intros w Hw. cbv zeta. unfold ent_op, ent_val. cbn [it_match].
  replace (w + 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (0 <=? w) with true by (symmetry; apply Z.leb_le; lia).
  split; [reflexivity|]. split; [reflexivity|].
  assert (E : exists k, w = Z.of_nat k /\ (k < 32)%nat) by (exists (Z.to_nat w); split; lia).
  destruct E as (k & -> & Hk).
  do 32 (destruct k as [|k];
    [ match goal with |- context [arr_get dext_a ?i] =>
        let v := eval vm_compute in (arr_get dext_a i) in replace (arr_get dext_a i) with v by (vm_compute; reflexivity) end;
      match goal with |- context [arr_get dbase_a ?i] =>
        let v := eval vm_compute in (arr_get dbase_a i) in replace (arr_get dbase_a i) with v by (vm_compute; reflexivity) end;
      rewrite w8_small by lia; lia |]). lia.
Qed.


Section Iface.
  Variables (ty : codetype) (lens : arr) (lens_ofs codes : Z) (tbl : arr) (table bits : Z) (work : arr).
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall s, 0 <= s < codes -> 0 <= arr_get lens (lens_ofs + s) <= 15.
  Hypothesis HtyC : ty = CODES -> codes <= 19 /\ bits = 7 /\ forall s, 0 <= s < codes -> arr_get lens (lens_ofs + s) <= 7.
  Hypothesis HtyD : ty = DISTS -> codes <= 32.
  Hypothesis Hbits : 1 <= bits <= 15.
  Hypothesis Htable : 0 <= table.
  Hypothesis Hroom : table + it_room ty <= arr_len tbl.
  Hypothesis Hwork : codes <= arr_len work.

  Local Notation r := (inflate_table ty lens lens_ofs codes tbl table bits work).
  Local Notation ret := (fst (fst (fst (fst r)))).
  Local Notation tbl' := (snd (fst (fst (fst r)))).
  Local Notation table' := (snd (fst (fst r))).
  Local Notation bits' := (snd (fst r)).

  Definition TERM (op val : Z) : Prop :=
    (op = 64 /\ val = 0) \/ (exists w, 0 <= w < codes /\ op = ent_op ty w /\ val = ent_val ty w).

  Definition root_cell (rb used e : Z) : Prop :=
    (exists op b val, e = code_pack op b val /\ 1 <= b <= rb /\ TERM op val)
    \/ (exists op val, e = code_pack op rb val /\ 1 <= op <= 15 - rb /\ 2 ^ rb <= val /\ val + 2 ^ op <= used).

  Definition sub_cell (rb e : Z) : Prop :=
    exists op b val, e = code_pack op b val /\ 1 <= b <= 15 - rb /\ TERM op val.

  Theorem it_shape : ret = 0 ->
    1 <= bits' <= 15 /\ (min lens lens_ofs codes <= bits -> bits' <= bits)
    /\ table + 2 ^ bits' <= table' <= table + it_room ty
    /\ arr_len tbl' = arr_len tbl
    /\ (forall x, 0 <= x < 2 ^ bits' -> root_cell bits' (table' - table) (arr_get tbl' (table + x)))
    /\ (forall i, table + 2 ^ bits' <= i < table' -> sub_cell bits' (arr_get tbl' i))
    /\ (forall i, ~ (table <= i < table') -> arr_get tbl' i = arr_get tbl i).
  Proof.
    intros Hret.
    pose proof (max_spec lens lens_ofs codes Hcodes Hlens) as (MA & MB & MC).
    pose proof (room2 ty tbl table Hroom) as R2.
    assert (TERM_INV : TERM 64 0) by (left; split; reflexivity).
    destruct (Z.eq_dec (max lens lens_ofs codes) 0) as [M0|M0].
    {
      rewrite (it_empty ty lens lens_ofs codes tbl table bits work M0) in *. cbn [fst snd] in *.
      change (2 ^ 1) with 2.
      split; [lia|]. split; [intros; lia|]. split; [destruct ty; cbn [it_room]; unfold ENOUGH_LENS, ENOUGH_DISTS; lia|].
      split; [rewrite !arr_len_set; reflexivity|].
      split.
      { intros x Hx. left. exists 64, 1, 0. split; [|split; [lia| exact TERM_INV]].
        destruct (Z.eq_dec x 1) as [->|NE].
        - apply arr_get_set_same. rewrite arr_len_set. lia.
        - rewrite arr_get_set_other by lia. replace (table + x) with table by lia. apply arr_get_set_same. lia. }
      split; [intros; lia|].
      intros i Hi. rewrite !(arr_get_set_other _ (table + 1)) by lia. rewrite !(arr_get_set_other _ table) by lia. reflexivity. }
    destruct (Z_lt_le_dec (2 ^ 15) (kraft lens lens_ofs codes 15)) as [K|K].
    { rewrite (it_over ty lens lens_ofs codes tbl table bits work Hcodes Hlens M0 K) in Hret. cbn in Hret. discriminate Hret. }
    destruct (Z.eq_dec (kraft lens lens_ofs codes 15) (2 ^ 15)) as [KC|KC].
    -
      set (root := itm_root bits (max lens lens_ofs codes) (min lens lens_ofs codes)) in *.
      pose proof (Hmax1 lens lens_ofs codes Hcodes Hlens M0) as M1.
      pose proof (Hroot lens lens_ofs codes bits Hcodes Hlens Hbits M0) as HR. fold root in HR.
      pose proof (CR lens lens_ofs codes Hcodes Hlens M1 root HR) as RR.
      pose proof (Lm lens lens_ofs codes Hcodes Hlens M1 root HR) as (Lm1 & Lm2 & Lm3).
      pose proof (CN lens lens_ofs codes Hcodes Hlens M1) as N1. pose proof (N_range lens lens_ofs codes Hcodes Hlens) as NR.
      destruct (it_not_enough ty (2 ^ root)) eqn:NE.
      { rewrite (it_big ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hbits Hroom M0 KC NE) in Hret. cbn in Hret. discriminate Hret. }
      set (kf := findZ (fun k => NF ty lens lens_ofs codes root k) 1 (N lens lens_ofs codes)).
      destruct (findZ_spec (fun k => NF ty lens lens_ofs codes root k) 1 (N lens lens_ofs codes) ltac:(lia)) as (R & P & Q). fold kf in R, P, Q.
      destruct (Z_lt_le_dec kf (N lens lens_ofs codes)) as [KF|KF].
      { destruct (it_fail ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hbits Hroom Hwork M0 KC NE
                    ltac:(exists kf; split; [lia | exact (P KF)])) as (A1 & _). cbv zeta in A1. rewrite A1 in Hret. discriminate Hret. }
      assert (HNF : forall k, 0 < k < N lens lens_ofs codes -> NF ty lens lens_ofs codes root k = false) by (intros k Hk; apply Q; lia).
      destruct (it_ok ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hbits Htable Hroom Hwork M0 KC NE HNF)
        as (A1 & T1 & B1 & L1 & G1 & _ & _ & _ & U1 & RB1 & RB1').
      cbv zeta in A1, T1, B1, L1, G1, U1. fold root in A1, T1, B1, G1, U1, RB1, RB1'.
      rewrite T1, B1. replace (table + usF lens lens_ofs codes root - table) with (usF lens lens_ofs codes root) by lia.
      split; [exact RB1|]. split; [exact RB1'|]. split; [lia|]. split; [exact L1|].
      pose proof (cover ty lens lens_ofs codes Hcodes Hlens M1 KC root HR table) as COV.
      pose proof (fun i v => LW_kind ty lens lens_ofs codes Hcodes Hlens M1 KC root HR table (Z.to_nat (N lens lens_ofs codes)) 0 i v
                             ltac:(lia) ltac:(lia)) as KIND.
      pose proof (fun i v => LW_range ty lens lens_ofs codes Hcodes Hlens M1 KC root HR table (Z.to_nat (N lens lens_ofs codes)) 0 i v
                             ltac:(lia) ltac:(lia)) as RANGE.
      split; [|split].
      + intros x Hx. rewrite G1.
        destruct (LW ty lens lens_ofs codes root table (Z.to_nat (N lens lens_ofs codes)) 0 (table + x)) as [v|] eqn:E;
          [| exfalso; exact (COV (table + x) ltac:(lia) E)].
        destruct (KIND (table + x) v E) as [(j & Hj & -> & Edr & Ecu & Enx & Hh & Hi) | [(k & Hk & Hnb & -> & Hik & Hi & Hcu & Hnx1 & Hnx2) | (j & Hj & -> & Edr & Hcu & Hh & Hnx & Hi & Hus)]].
        * left. unfold HV. rewrite Edr, Z.sub_0_r. eexists _, _, _. split; [reflexivity|].
          pose proof (CL lens lens_ofs codes Hcodes j ltac:(lia)). pose proof (Lm2 j Hj). split; [lia|].
          right. exists (znth 0 (W lens lens_ofs codes) j). split; [apply (LWr lens lens_ofs codes Hcodes); lia|]. split; reflexivity.
        * right. unfold LINK. eexists _, _. split; [reflexivity|]. split; [exact Hcu|]. lia.
        * exfalso. lia.
      + intros i Hi. rewrite G1.
        destruct (LW ty lens lens_ofs codes root table (Z.to_nat (N lens lens_ofs codes)) 0 i) as [v|] eqn:E;
          [| exfalso; exact (COV i ltac:(lia) E)].
        destruct (KIND i v E) as [(j & Hj & -> & Edr & Ecu & Enx & Hh & Hi2) | [(k & Hk & Hnb & -> & Hik & Hi2 & Hcu & Hnx1 & Hnx2) | (j & Hj & -> & Edr & Hcu & Hh & Hnx & Hi2 & Hus)]].
        * exfalso. lia.
        * exfalso. lia.
        * unfold HV. rewrite Edr. eexists _, _, _. split; [reflexivity|].
          pose proof (CL lens lens_ofs codes Hcodes j ltac:(lia)). pose proof (Lm3 j Hj). split; [lia|].
          right. exists (znth 0 (W lens lens_ofs codes) j). split; [apply (LWr lens lens_ofs codes Hcodes); lia|]. split; reflexivity.
      + intros i Hi. rewrite G1.
        destruct (LW ty lens lens_ofs codes root table (Z.to_nat (N lens lens_ofs codes)) 0 i) as [v|] eqn:E; [|reflexivity].
        exfalso. apply Hi. exact (RANGE i v E).
    -
      assert (KL : kraft lens lens_ofs codes 15 < 2 ^ 15) by lia.
      destruct (codetype_eqb ty CODES || negb (max lens lens_ofs codes =? 1)) eqn:E.
      { assert (C : ty = CODES \/ max lens lens_ofs codes <> 1).
        { apply Bool.orb_true_iff in E. destruct E as [E|E]; [left; destruct ty; [reflexivity|discriminate|discriminate] | right].
          apply negb_true_iff in E. apply Z.eqb_neq in E. exact E. }
        rewrite (it_incomp ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hroom M0 KL C) in Hret. cbn in Hret. discriminate Hret. }
      apply Bool.orb_false_iff in E. destruct E as [E1 E2]. apply negb_false_iff in E2. apply Z.eqb_eq in E2.
      assert (Hty : ty <> CODES) by (intros X; rewrite X in E1; discriminate).
      destruct (single_facts lens lens_ofs codes bits Hcodes Hlens Hbits E2 KL) as (C1 & N1 & MN & RT & Wr & WL).
      destruct (it_single ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hbits Htable Hroom Hwork E2 KL Hty)
        as (A1 & T1 & B1 & L1 & G1 & _).
      cbv zeta in A1, T1, B1, L1, G1. rewrite T1, B1. change (2 ^ 1) with 2.
      split; [lia|]. split; [intros; lia|]. split; [destruct ty; cbn [it_room]; unfold ENOUGH_LENS, ENOUGH_DISTS; lia|].
      split; [exact L1|].
      split.
      { intros x Hx. rewrite G1. left. destruct (Z.eqb_spec (table + x) (table + 1)) as [E|NE].
        - exists 64, 1, 0. split; [reflexivity|]. split; [lia | exact TERM_INV].
        - replace (table + x =? table) with true by (symmetry; apply Z.eqb_eq; lia).
          eexists _, _, _. split; [reflexivity|]. split; [lia|]. right. exists (znth 0 (W lens lens_ofs codes) 0).
          split; [exact Wr|]. split; reflexivity. }
      split; [intros; lia|].
      intros i Hi. rewrite G1. replace (i =? table + 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (i =? table) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  Qed.
End Iface.


Lemma it_step_lens : forall x st,
  match it_step x st with ItCont st' | ItBreak st' | ItFail st' =>
    arr_len (t_tbl st') = arr_len (t_tbl st) /\ t_work st' = t_work st end.
Proof.
  intros x st. destruct st as [huff sym len next curr drop low used mn0 count tbl work].
  cbv beta iota zeta delta [it_step t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work].
  destruct (if arr_get work sym + 1 <? it_match (x_ty x) then (0, arr_get work sym)
            else if it_match (x_ty x) <=? arr_get work sym
            then (wrap8 (it_extra (x_ty x) work (arr_get work sym - it_match (x_ty x))), it_base (x_ty x) work (arr_get work sym - it_match (x_ty x)))
            else (96, 0)) as [here_op here_val].
  destruct (_ && (len =? x_max x)); cbn [t_tbl t_work]; [split; [apply it_fill_len | reflexivity]|].
  destruct (_ && negb _); [| cbn [t_tbl t_work]; split; [apply it_fill_len | reflexivity]].
  destruct (it_not_enough _ _); cbn [t_tbl t_work]; [split; [apply it_fill_len | reflexivity]|].
  rewrite arr_len_set. split; [apply it_fill_len | reflexivity].
Qed.

Lemma it_loop_n_lens : forall (n : nat) x st,
  match it_loop_n x (Z.of_nat n) st with inl st' | inr st' =>
    arr_len (t_tbl st') = arr_len (t_tbl st) /\ t_work st' = t_work st end.
Proof.
  induction n as [|n IH]; intros x st.
  - unfold it_loop_n. rewrite iterZ_le0 by lia. split; reflexivity.
  - rewrite it_loop_n_step by lia. replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    pose proof (it_step_lens x st) as SL.
    destruct (it_step x st) as [st1|st1|st1]; [| exact SL | exact SL].
    destruct SL as [L1 W1]. pose proof (IH x st1) as IHn.
    destruct (it_loop_n x (Z.of_nat n) st1) as [st2|st2]; destruct IHn as [L2 W2]; split; congruence.
Qed.

Theorem inflate_table_lengths : forall ty lens lens_ofs codes tbl table bits work,
  let r := inflate_table ty lens lens_ofs codes tbl table bits work in
  arr_len (snd (fst (fst (fst r)))) = arr_len tbl /\ arr_len (snd r) = arr_len work.
Proof.
  intros ty lens lens_ofs codes tbl table bits work. cbv zeta. rewrite inflate_table_phases. cbv zeta.
  pose proof (itm_sort_k_len lens lens_ofs codes (itm_offs (itm_count lens lens_ofs codes)) work) as [_ WL].
  assert (WE : arr_len (itm_work lens lens_ofs codes (itm_offs (itm_count lens lens_ofs codes)) work) = arr_len work).
  { rewrite itm_work_eq. exact WL. }
  destruct (itm_max _ =? 0); [cbn [fst snd]; rewrite !arr_len_set; split; reflexivity|].
  destruct (itm_reject _ _ _); [cbn [fst snd]; split; reflexivity|].
  destruct (it_not_enough _ _); [cbn [fst snd]; split; [reflexivity | exact WE]|].
  rewrite it_loop_is_n.
  destruct (Z_lt_le_dec codes 0) as [Hc|Hc].
  - unfold it_loop_n. rewrite iterZ_le0 by lia. cbn [fst snd t_huff t_tbl t_next t_len t_drop t_used t_work itm_st0].
    destruct (negb _); cbn [fst snd]; [rewrite arr_len_set|]; split; try reflexivity; exact WE.
  - replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia.
    pose proof (it_loop_n_lens (Z.to_nat (codes + 1)) (itm_ctx ty lens lens_ofs table (itm_root bits (itm_max (itm_count lens lens_ofs codes))
                  (itm_min (itm_count lens lens_ofs codes) (itm_max (itm_count lens lens_ofs codes)))) (itm_max (itm_count lens lens_ofs codes)))
                  (itm_st0 (itm_min (itm_count lens lens_ofs codes) (itm_max (itm_count lens lens_ofs codes))) table
                     (itm_root bits (itm_max (itm_count lens lens_ofs codes)) (itm_min (itm_count lens lens_ofs codes) (itm_max (itm_count lens lens_ofs codes))))
                     (itm_count lens lens_ofs codes) tbl (itm_work lens lens_ofs codes (itm_offs (itm_count lens lens_ofs codes)) work))) as LL.
    destruct (it_loop_n _ _ _) as [st|st]; unfold itm_st0 in LL; cbn [t_tbl t_work] in LL; destruct LL as [L1 W1]; cbn [fst snd].
    + destruct (negb _); [rewrite arr_len_set|]; rewrite L1, W1; split; try reflexivity; exact WE.
    + rewrite L1, W1. split; [reflexivity | exact WE].
Qed.

Theorem inflate_table_fail_shape : forall ty lens lens_ofs codes tbl table bits work,
  let r := inflate_table ty lens lens_ofs codes tbl table bits work in
  fst (fst (fst (fst r))) <> 0 -> snd (fst (fst r)) = table /\ snd (fst r) = bits.
Proof.
  intros ty lens lens_ofs codes tbl table bits work. cbv zeta. rewrite inflate_table_phases. cbv zeta.
  destruct (itm_max _ =? 0); [cbn [fst snd]; intros H; exfalso; apply H; reflexivity|].
  destruct (itm_reject _ _ _); [cbn [fst snd]; intros _; split; reflexivity|].
  destruct (it_not_enough _ _); [cbn [fst snd]; intros _; split; reflexivity|].
  destruct (it_loop _ _ _) as [st|st]; cbn [fst snd].
  - intros H; exfalso; apply H; reflexivity.
  - intros _; split; reflexivity.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees ModelRel InftreesCoverage ItableModel InflateGarbBase
  ItCovBits ItCovPre ItCovMath ItCovStep ItCovLoop ItCovMain ItCovIface InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import ItAPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Ltac lia_std := lia.


Lemma andb_true2 : forall a b, a = true -> b = true -> a && b = true.
Proof. intros [] [] A B; try discriminate; reflexivity. Qed.
Lemma leb_true : forall a b, a <= b -> (a <=? b) = true. Proof. intros. apply Z.leb_le. assumption. Qed.
Lemma ltb_true : forall a b, a < b -> (a <? b) = true. Proof. intros. apply Z.ltb_lt. assumption. Qed.
Lemma eqb_true : forall a b, a = b -> (a =? b) = true. Proof. intros. apply Z.eqb_eq. assumption. Qed.
Lemma linkop_false_of : forall op, op = 0 \/ 16 <= op -> is_linkop op = false.
Proof. intros op H. unfold is_linkop. destruct (Z.leb_spec 1 op); destruct (Z.leb_spec op 15); cbn; try reflexivity; lia_std. Qed.

Lemma term_ok_pack : forall ty codes maxb op b val,
  (ty = CODES -> codes <= 19) -> (ty = DISTS -> codes <= 32) -> codes <= 288 ->
  1 <= b <= maxb -> maxb <= 15 -> TERM ty codes op val ->
  is_linkop (code_op (code_pack op b val)) = false /\ term_ok ty maxb (code_pack op b val) = true.
Proof.
  intros ty codes maxb op b val HC HD H288 Hb Hmb T.
  unfold term_ok. rewrite code_op_pack, code_bits_pack, code_val_pack. rewrite (w8_small b) by lia_std.
  assert (BB : (1 <=? b) && (b <=? maxb) = true) by (apply andb_true2; apply leb_true; lia_std).
  destruct T as [[-> ->] | (w & Hw & -> & ->)].
  - change (wrap8 64) with 64. change (wrap16 0) with 0. split; [apply linkop_false_of; lia_std|].
    rewrite BB. destruct ty; reflexivity.
  - destruct ty.
    + destruct (ent_CODES w ltac:(specialize (HC eq_refl); lia_std)) as [Eo Ev]. rewrite Eo. change (wrap8 0) with 0.
      split; [apply linkop_false_of; lia_std|]. rewrite BB. reflexivity.
    + pose proof (ent_LENS_L w ltac:(lia_std)) as L. cbv zeta in L.
      destruct L as [(Eo & Ev & Hw2) | [(Eo & Ev) | [[Eo | Eo] | (Ho & Hv & HvL)]]]; rewrite ?Eo, ?Ev.
      * change (wrap8 0) with 0. rewrite (w16_small w) by lia_std. split; [apply linkop_false_of; lia_std|]. rewrite BB. cbn [Z.eqb andb orb].
        rewrite (ltb_true w 256) by lia_std. reflexivity.
      * change (wrap8 96) with 96. split; [apply linkop_false_of; lia_std|]. rewrite BB. reflexivity.
      * change (wrap8 71) with 71. split; [apply linkop_false_of; lia_std|]. rewrite BB. reflexivity.
      * change (wrap8 77) with 77. split; [apply linkop_false_of; lia_std|]. rewrite BB. reflexivity.
      * destruct (op_base_tests (ent_op LENS w) ltac:(lia_std)) as (E16 & E64 & _ & _ & E15 & _).
        rewrite (w8_small (ent_op LENS w)) by lia_std.
        assert (V16 : wrap16 (ent_val LENS w) = ent_val LENS w).
        { apply w16_small. assert (0 < 2 ^ Z.land (ent_op LENS w) 15) by (apply Z.pow_pos_nonneg; lia_std). lia_std. }
        rewrite V16. rewrite E15 in HvL.
        split; [apply linkop_false_of; lia_std|]. rewrite BB.
        apply Bool.orb_true_intro. left. apply Bool.orb_true_intro. right.
        rewrite (leb_true 16), (leb_true _ 21), (leb_true 3) by lia_std. cbn [andb]. apply leb_true. rewrite Z.shiftl_1_l. lia_std.
    + pose proof (ent_DISTS w ltac:(specialize (HD eq_refl); lia_std)) as L. cbv zeta in L.
      destruct L as (Eo & Ev & [(Ho & Hv) | (Ho & Hw30)]).
      * destruct (op_base_tests (ent_op DISTS w) ltac:(lia_std)) as (_ & _ & _ & _ & E15 & _).
        rewrite (w8_small (ent_op DISTS w)), (w16_small (ent_val DISTS w)) by lia_std.
        split; [apply linkop_false_of; lia_std|]. rewrite BB.
        apply Bool.orb_true_intro. left.
        rewrite (leb_true 16), (leb_true _ 29), (leb_true 1) by lia_std. cbn [andb]. apply leb_true. rewrite Z.shiftl_1_l.
        assert (P : 2 ^ (ent_op DISTS w - 16) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 13) with 8192 in P. lia_std.
      * rewrite Ho. change (wrap8 64) with 64. split; [apply linkop_false_of; lia_std|]. rewrite BB. reflexivity.
Qed.

Lemma code_pack_range : forall op b v, 0 <= code_pack op b v < 2 ^ 32.
Proof. intros op b v. unfold code_pack. pose proof (w8_range op). pose proof (w8_range b). pose proof (w16_range v). lia_std. Qed.


Section Bridge.
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

  Theorem tab_ok_of_shape : it_ret r = 0 ->
    tab_ok ty (cat (it_tbl r) (CDyn table)) (it_bits r) (it_table r - table) = true
    /\ 1 <= it_bits r <= 15 /\ table + 2 ^ it_bits r <= it_table r <= table + it_room ty
    /\ arr_len (it_tbl r) = arr_len tbl
    /\ (forall i, ~ (table <= i < it_table r) -> arr_get (it_tbl r) i = arr_get tbl i).
  Proof.
    unfold it_ret, it_tbl, it_bits, it_table. intros Hret.
    destruct (it_shape ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hbits Htable Hroom Hwork Hret)
      as (B1 & B2 & T1 & L1 & ROOT & SUB & OUT).
    assert (HC : ty = CODES -> codes <= 19) by (intros E; apply (proj1 (HtyC E))).
    split; [| split; [lia_std | split; [exact T1 | split; [exact L1 | exact OUT]]]].
    unfold tab_ok, cat. apply andb_true_intro. split.
    { repeat (apply andb_true_intro; split); apply Z.leb_le; try lia_std. rewrite Z.shiftl_1_l. lia_std. }
    apply forallb_forall. intros x Hx. apply zupto_spec in Hx. rewrite Z.shiftl_1_l in Hx.
    unfold root_ok. destruct (ROOT x Hx) as [(op & b & val & E & Hb & T) | (op & val & E & Hop & Hval & Hused)]; rewrite E.
    - destruct (term_ok_pack ty codes _ op b val HC HtyD ltac:(lia_std) Hb ltac:(lia_std) T) as [NL TM]. rewrite NL. exact TM.
    - unfold is_linkop at 1. rewrite code_op_pack, code_bits_pack, code_val_pack.
      rewrite (w8_small op), (w8_small _) by lia_std.
      assert (V : wrap16 val = val).
      { apply w16_small. assert (0 < 2 ^ op) by (apply Z.pow_pos_nonneg; lia_std).
        assert (it_room ty <= 852) by (destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia_std). lia_std. }
      rewrite V.
      replace ((1 <=? op) && (op <=? 15)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia_std).
      apply andb_true_intro. split.
      + repeat (apply andb_true_intro; split); try (apply Z.leb_le; rewrite ?Z.shiftl_1_l; lia_std). apply Z.eqb_eq. reflexivity.
      + apply forallb_forall. intros j Hj. apply zupto_spec in Hj. rewrite Z.shiftl_1_l in Hj. cbv beta.
        destruct (SUB (table + (val + j)) ltac:(lia_std)) as (op2 & b2 & val2 & E2 & Hb2 & T2).
        rewrite E2.
        destruct (term_ok_pack ty codes _ op2 b2 val2 HC HtyD ltac:(lia_std) Hb2 ltac:(lia_std) T2) as [NL TM]. rewrite NL, TM. reflexivity.
  Qed.
End Bridge.


Lemma tab_ok_ext_rd : forall ty rd rd' root ext,
  (forall i, 0 <= i < ext -> rd' i = rd i) -> tab_ok ty rd root ext = true -> tab_ok ty rd' root ext = true.
Proof. intros. eapply tab_ok_ext; eassumption. Qed.

Theorem tab_ok_of_itable :
  forall (ty : codetype) (lf cf wf cf' : Z -> Z) (lens_ofs codes nx bits : Z),
  let r := inflate_table ty (arr_init N_LENS lf) lens_ofs codes (arr_init N_CODES cf) nx bits (arr_init N_WORK wf) in
  0 <= lens_ofs -> lens_ofs + codes <= N_LENS -> 0 <= codes -> codes <= 288 ->
  (forall i, 0 <= i < N_LENS -> 0 <= lf i < 65536) ->
  (forall s, 0 <= s < codes -> lf (lens_ofs + s) <= 15) ->
  (ty = CODES -> codes <= 19 /\ bits = 7 /\ (forall s, 0 <= s < codes -> lf (lens_ofs + s) <= 7)) ->
  (ty = DISTS -> codes <= 32) ->
  1 <= bits -> bits <= 15 -> 0 <= nx -> nx + it_room ty <= N_CODES ->
  it_ret r = 0 ->
  (forall i, 0 <= i < N_CODES -> cf' i = arr_get (it_tbl r) i) ->
  tab_ok ty (rdc cf' (CDyn nx)) (it_bits r) (it_table r - nx) = true
  /\ 1 <= it_bits r <= 15 /\ nx + 2 ^ it_bits r <= it_table r <= nx + it_room ty
  /\ (forall i, 0 <= i < N_CODES -> ~ (nx <= i < it_table r) -> cf' i = cf i).
Proof.
  intros ty lf cf wf cf' lens_ofs codes nx bits r Ho1 Ho2 Hc0 Hc1 Hlf Hl15 HC HD Hb1 Hb2 Hnx Hroom Hret Hcf'. subst r.
  assert (AL : forall i, arr_get (arr_init N_LENS lf) i = lf i) by (intros i; apply arr_get_init).
  assert (Hlens : forall s, 0 <= s < codes -> 0 <= arr_get (arr_init N_LENS lf) (lens_ofs + s) <= 15).
  { intros s Hs. rewrite AL. split; [| apply Hl15; lia_std].
    assert (R : 0 <= lens_ofs + s < N_LENS) by (unfold N_LENS in *; lia_std). exact (proj1 (Hlf _ R)). }
  assert (HtyC : ty = CODES -> codes <= 19 /\ bits = 7 /\ forall s, 0 <= s < codes -> arr_get (arr_init N_LENS lf) (lens_ofs + s) <= 7).
  { intros E. destruct (HC E) as (A & B & C). split; [exact A | split; [exact B |]]. intros s Hs. rewrite AL. apply C. lia_std. }
  assert (Hroom' : nx + it_room ty <= arr_len (arr_init N_CODES cf)) by (rewrite arr_len_init; unfold N_CODES in *; lia_std).
  assert (Hwork : codes <= arr_len (arr_init N_WORK wf)) by (rewrite arr_len_init; unfold N_WORK; lia_std).
  destruct (tab_ok_of_shape ty (arr_init N_LENS lf) lens_ofs codes (arr_init N_CODES cf) nx bits (arr_init N_WORK wf)
              ltac:(lia_std) Hlens HtyC HD ltac:(lia_std) Hnx Hroom' Hwork Hret) as (T & B & TT & L & OUT).
  split; [| split; [exact B | split; [exact TT |]]].
  2:{ intros i Hi Hout. rewrite (Hcf' i Hi), (OUT i Hout). apply arr_get_init. }
  eapply tab_ok_ext_rd; [| exact T].
  intros i Hi. unfold rdc, cat. apply Hcf'.
  assert (it_room ty >= 0) by (destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia_std). unfold N_CODES in *. lia_std.
Qed.

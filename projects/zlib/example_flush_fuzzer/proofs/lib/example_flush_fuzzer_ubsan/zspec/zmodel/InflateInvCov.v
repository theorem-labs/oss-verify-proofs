(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InftreesCoverage ItCovLoop ItCovMain ItCovIface ItCovRep.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInv InflateInvTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma andb_true2 : forall a b, a = true -> b = true -> a && b = true.
Proof. intros [] [] A B; try discriminate; reflexivity. Qed.
Lemma leb_true : forall a b, a <= b -> (a <=? b) = true. Proof. intros. apply Z.leb_le. assumption. Qed.
Lemma ltb_true : forall a b, a < b -> (a <? b) = true. Proof. intros. apply Z.ltb_lt. assumption. Qed.
Lemma linkop_false_of : forall op, op = 0 \/ 16 <= op -> is_linkop op = false.
Proof. intros op H. unfold is_linkop. destruct (Z.leb_spec 1 op); destruct (Z.leb_spec op 15); cbn; try reflexivity; lia. Qed.

Lemma term_ok_pack : forall ty codes maxb op b val,
  (ty = CODES -> codes <= 19) -> (ty = DISTS -> codes <= 32) -> codes <= 288 ->
  1 <= b <= maxb -> maxb <= 15 -> TERM ty codes op val ->
  is_linkop (code_op (code_pack op b val)) = false /\ term_ok ty maxb (code_pack op b val) = true.
Proof.
  intros ty codes maxb op b val HC HD H288 Hb Hmb T.
  unfold term_ok. rewrite code_op_pack, code_bits_pack, code_val_pack. rewrite (w8_small b) by lia.
  assert (BB : (1 <=? b) && (b <=? maxb) = true) by (apply andb_true2; apply leb_true; lia).
  destruct T as [[-> ->] | (w & Hw & -> & ->)].
  - change (wrap8 64) with 64. change (wrap16 0) with 0. split; [apply linkop_false_of; lia|].
    rewrite BB. destruct ty; reflexivity.
  - destruct ty.
    + destruct (ent_CODES w ltac:(specialize (HC eq_refl); lia)) as [Eo Ev]. rewrite Eo. change (wrap8 0) with 0.
      split; [apply linkop_false_of; lia|]. rewrite BB. reflexivity.
    + pose proof (ent_LENS_L w ltac:(lia)) as L. cbv zeta in L.
      destruct L as [(Eo & Ev & Hw2) | [(Eo & Ev) | [[Eo | Eo] | (Ho & Hv & HvL)]]]; rewrite ?Eo, ?Ev.
      * change (wrap8 0) with 0. rewrite (w16_small w) by lia. split; [apply linkop_false_of; lia|]. rewrite BB. cbn [Z.eqb andb orb].
        rewrite (ltb_true w 256) by lia. reflexivity.
      * change (wrap8 96) with 96. split; [apply linkop_false_of; lia|]. rewrite BB. reflexivity.
      * change (wrap8 71) with 71. split; [apply linkop_false_of; lia|]. rewrite BB. reflexivity.   (* 1.4: lext[29] = 71 *)
      * change (wrap8 77) with 77. split; [apply linkop_false_of; lia|]. rewrite BB. reflexivity.
      * destruct (op_base_tests (ent_op LENS w) ltac:(lia)) as (E16 & E64 & _ & _ & E15 & _).
        rewrite (w8_small (ent_op LENS w)) by lia.
        assert (V16 : wrap16 (ent_val LENS w) = ent_val LENS w).
        { apply w16_small. assert (0 < 2 ^ Z.land (ent_op LENS w) 15) by (apply Z.pow_pos_nonneg; lia). lia. }
        rewrite V16. rewrite E15 in HvL.
        split; [apply linkop_false_of; lia|]. rewrite BB.
        apply Bool.orb_true_intro. left. apply Bool.orb_true_intro. right.
        rewrite (leb_true 16), (leb_true _ 21), (leb_true 3) by lia. cbn [andb]. apply leb_true. rewrite Z.shiftl_1_l. lia.
    + pose proof (ent_DISTS w ltac:(specialize (HD eq_refl); lia)) as L. cbv zeta in L.
      destruct L as (Eo & Ev & [(Ho & Hv) | (Ho & Hw30)]).
      * destruct (op_base_tests (ent_op DISTS w) ltac:(lia)) as (_ & _ & _ & _ & E15 & _).
        rewrite (w8_small (ent_op DISTS w)), (w16_small (ent_val DISTS w)) by lia.
        split; [apply linkop_false_of; lia|]. rewrite BB.
        apply Bool.orb_true_intro. left.
        rewrite (leb_true 16), (leb_true _ 29), (leb_true 1) by lia. cbn [andb]. apply leb_true. rewrite Z.shiftl_1_l.
        assert (P : 2 ^ (ent_op DISTS w - 16) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in P. lia.
      * rewrite Ho. change (wrap8 64) with 64. split; [apply linkop_false_of; lia|]. rewrite BB. reflexivity.
Qed.

Lemma code_pack_range : forall op b v, 0 <= code_pack op b v < 2 ^ 32.
Proof. intros op b v. unfold code_pack. pose proof (w8_range op). pose proof (w8_range b). pose proof (w16_range v). lia. Qed.


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
  Local Notation ret := (fst (fst (fst (fst r)))).
  Local Notation tbl' := (snd (fst (fst (fst r)))).
  Local Notation table' := (snd (fst (fst r))).
  Local Notation bits' := (snd (fst r)).

  Theorem tab_ok_of_shape : ret = 0 ->
    tab_ok ty (cat tbl' (CDyn table)) bits' (table' - table) = true
    /\ 1 <= bits' <= 15 /\ table + 2 ^ bits' <= table' <= table + it_room ty
    /\ arr_len tbl' = arr_len tbl
    /\ (forall i, ~ (table <= i < table') -> arr_get tbl' i = arr_get tbl i).
  Proof.
    intros Hret.
    destruct (it_shape ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hbits Htable Hroom Hwork Hret)
      as (B1 & B2 & T1 & L1 & ROOT & SUB & OUT).
    assert (HC : ty = CODES -> codes <= 19) by (intros E; apply (proj1 (HtyC E))).
    split; [| split; [lia | split; [exact T1 | split; [exact L1 | exact OUT]]]].
    unfold tab_ok, cat. apply andb_true_intro. split.
    { repeat (apply andb_true_intro; split); apply Z.leb_le; try lia. rewrite Z.shiftl_1_l. lia. }
    apply forallb_forall. intros x Hx. apply zupto_spec in Hx. rewrite Z.shiftl_1_l in Hx.
    unfold root_ok. destruct (ROOT x Hx) as [(op & b & val & E & Hb & T) | (op & val & E & Hop & Hval & Hused)]; rewrite E.
    - destruct (term_ok_pack ty codes bits' op b val HC HtyD ltac:(lia) Hb ltac:(lia) T) as [NL TM]. rewrite NL. exact TM.
    - unfold is_linkop at 1. rewrite code_op_pack, code_bits_pack, code_val_pack.
      rewrite (w8_small op), (w8_small bits') by lia.
      assert (V : wrap16 val = val).
      { apply w16_small. assert (0 < 2 ^ op) by (apply Z.pow_pos_nonneg; lia).
        assert (it_room ty <= 852) by (destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia). lia. }
      rewrite V.
      replace ((1 <=? op) && (op <=? 15)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
      apply andb_true_intro. split.
      + repeat (apply andb_true_intro; split); try (apply Z.leb_le; rewrite ?Z.shiftl_1_l; lia). apply Z.eqb_eq. reflexivity.
      + apply forallb_forall. intros j Hj. apply zupto_spec in Hj. rewrite Z.shiftl_1_l in Hj. cbv beta.
        destruct (SUB (table + (val + j)) ltac:(lia)) as (op2 & b2 & val2 & E2 & Hb2 & T2).
        replace (table + (val + j)) with (table + (val + j)) by lia. rewrite E2.
        destruct (term_ok_pack ty codes (15 - bits') op2 b2 val2 HC HtyD ltac:(lia) Hb2 ltac:(lia) T2) as [NL TM]. rewrite NL, TM. reflexivity.
  Qed.

  Theorem rep_ok_of_shape : ret = 0 -> rep_ok (cat tbl' (CDyn table)) bits'.
  Proof.
    intros Hret.
    destruct (it_replicated ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hbits Htable Hroom Hwork Hret) as [RR RS].
    unfold it_rep_root in RR. unfold it_rep_sub in RS. cbv zeta in RR, RS.
    unfold rep_ok, cat. split.
    - intros x x' Hx Hx' NL E. apply (RR x x' Hx Hx'); [| exact E].
      intros L. apply (proj2 (is_linkop_true _)) in L. rewrite L in NL. discriminate NL.
    - intros x Hx L i i' Hi Hi' E. apply (proj1 (is_linkop_true _)) in L.
      rewrite !Z.add_assoc. rewrite !Z.add_assoc in E. apply (RS x Hx L i i' Hi Hi' E).
  Qed.
End Bridge.

Lemma rep_ok_ext : forall ty rd rd' root ext,
  tab_ok ty rd root ext = true -> (forall i, 0 <= i < ext -> rd' i = rd i) -> rep_ok rd root -> rep_ok rd' root.
Proof.
  intros ty rd rd' root ext T E [RR RS]. destruct (tab_ok_root _ _ _ _ T) as (R1 & R2 & R3).
  assert (ER : forall x, 0 <= x < 2 ^ root -> rd' x = rd x) by (intros x Hx; apply E; lia).
  split.
  - intros x x' Hx Hx' NL M. rewrite !ER in * by lia. apply (RR x x' Hx Hx' NL M).
  - intros x Hx L i i' Hi Hi' M. rewrite (ER x Hx) in *.
    pose proof (tab_root_entry ty rd root ext x T Hx) as RT. cbv beta in RT.
    destruct RT as (_ & _ & _ & [[NL _] | (OP & BR & VR & XR & SUB)]); [rewrite NL in L; discriminate L|].
    rewrite !E in * by lia. apply (RS x Hx L i i' Hi Hi' M).
Qed.


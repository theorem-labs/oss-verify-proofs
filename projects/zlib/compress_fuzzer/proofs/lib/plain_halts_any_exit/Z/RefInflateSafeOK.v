(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac munf := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY,
  TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.
Ltac mode_lit E := first [ apply Z.eqb_eq in E | apply Bool.orb_true_iff in E; destruct E as [E|E]; mode_lit E ].

Lemma adler_canon_b_true : forall a, adler_canon a -> adler_canon_b a = true.
Proof.
  intros a (H1 & H2 & H3). unfold adler_canon_b.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma leave_okb_of_canon : forall s, (is_flags s = 0 -> adler_canon (is_check s)) -> leave_okb s = true.
Proof.
  intros s H. unfold leave_okb. destruct (Z.eqb_spec (is_flags s) 0) as [F|F].
  - rewrite (adler_canon_b_true _ (H F)). rewrite !Bool.orb_true_r. reflexivity.
  - cbn [negb]. rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma MF_canon : forall m s h b, MF m s h b -> m <> DICT -> m <> MEM -> (is_flags s = 0 -> adler_canon (is_check s)).
Proof.
  intros m s h b HM ND NM. unfold MF, common, tables in HM. revert HM.
  repeat match goal with |- (if ?c then _ else _) -> _ =>
    let E := fresh "E" in destruct c eqn:E;
    [ mode_lit E; first [ exfalso; congruence
                        | intros X; decompose [and] X; first [ assumption | intros _; assumption ] ] |] end.
  intros X. destruct X.
Qed.

Theorem WINV_leave_okb : forall w, WINV w -> is_mode (w_s w) <> DICT -> is_mode (w_s w) <> MEM -> leave_okb (w_s w) = true.
Proof.
  intros [s c r] HW ND NM. unfold WINV in HW. cbn [w_s w_c w_r] in HW, ND, NM |- *. destruct HW as (_ & _ & HMF & _).
  apply leave_okb_of_canon. exact (MF_canon _ _ _ _ HMF ND NM).
Qed.

Theorem WINV_distext_okb : forall w, WINV w -> is_mode (w_s w) = DISTEXT -> distext_okb (w_s w) = true.
Proof.
  intros [s c r] HW E. unfold WINV in HW. cbn [w_s w_c w_r] in HW, E |- *. destruct HW as (_ & _ & HMF & _).
  rewrite E in HMF. revert HMF. mred. intros (_ & _ & _ & _ & X & _). unfold distext_okb. apply Z.leb_le. lia.
Qed.

Theorem WINV_lenext_okb : forall w, WINV w -> is_mode (w_s w) = LENEXT -> lenext_okb (w_s w) = true.
Proof.
  intros [s c r] HW E. unfold WINV in HW. cbn [w_s w_c w_r] in HW, E |- *. destruct HW as (_ & _ & HMF & _).
  rewrite E in HMF. revert HMF. mred. intros (_ & _ & _ & X & _). unfold lenext_okb. apply Z.leb_le. lia.
Qed.

Section Dchk.
  Variable c : icall.

  Lemma dchk_ok : forall k index need N tab r,
    REGS c r ->
    (forall h, 0 <= h -> 0 <= index h < N) ->
    (forall h, 0 <= h -> 1 <= need (tab (index h)) <= 15) ->
    16 <= 8 * Z.of_nat k + ir_bits r ->
    exists r', dchk k c index need N tab r = Some r' /\ REGS c r'.
  Proof.
    induction k as [|k IH]; intros index need N tab r HR HI HN HK.
    - cbn [dchk]. pose proof HR as (_ & _ & _ & _ & _ & _ & [Bb Bh] & _).
      pose proof (HI (ir_hold r) ltac:(lia)) as I1. pose proof (HN (ir_hold r) ltac:(lia)) as N1.
      rewrite (proj2 (Z.leb_le _ _) (proj1 I1)), (proj2 (Z.ltb_lt _ _) (proj2 I1)).
      rewrite (proj2 (Z.leb_le 0 _)) by lia. rewrite (proj2 (Z.leb_le _ 32)) by lia. cbn [andb].
      cbn [Z.of_nat] in HK. rewrite (proj2 (Z.leb_le _ _)) by lia. exists r. split; [reflexivity|exact HR].
    - cbn [dchk]. pose proof HR as (_ & Hh0 & _ & _ & _ & _ & [Bb Bh] & _).
      pose proof (HI (ir_hold r) ltac:(lia)) as I1. pose proof (HN (ir_hold r) ltac:(lia)) as N1.
      rewrite (proj2 (Z.leb_le _ _) (proj1 I1)), (proj2 (Z.ltb_lt _ _) (proj2 I1)).
      rewrite (proj2 (Z.leb_le 0 _)) by lia. rewrite (proj2 (Z.leb_le _ 32)) by lia. cbn [andb].
      destruct (Z.leb_spec (need (tab (index (ir_hold r)))) (ir_bits r)) as [L|L].
      + exists r. split; [reflexivity|exact HR].
      + destruct (Z.eqb_spec (ir_have r) 0) as [Z0|Z0].
        * exists r. split; [reflexivity|exact HR].
        * destruct (REGS_pullr c r HR ltac:(lia) ltac:(lia)) as (HR1 & _ & B1 & _).
          apply (IH index need N tab (pullr c r) HR1 HI HN). rewrite B1. rewrite Nat2Z.inj_succ in HK. lia.
  Qed.
End Dchk.

Lemma BITSv_range : forall h n, 0 <= h -> 0 <= n <= 32 -> 0 <= BITSv h n < 2 ^ n.
Proof. intros h n Hh Hn. rewrite BITSv_mod by lia. apply Z.mod_pos_bound. apply pow2_pos. lia. Qed.

Lemma decode_okb_TBLg : forall two ty s c r p root used,
  ty <> CODES ->
  TBLg ty (code_at s p) root used -> used <= ctab_size p -> REGS c r ->
  (forall e, ((exists sy, 0 <= sy < nsyms ty /\ code_op e = fst (sym_entry ty sy) /\ code_val e = snd (sym_entry ty sy)) \/ code_op e = 64) ->
             two (code_op e) = true -> False) ->
  decode_okb two s c r p root = true.
Proof.
  intros two ty s c r p root used Hty HT HU HR Hcontra.
  pose proof (T_root _ _ _ _ HT) as R15. pose proof (T_used _ _ _ _ HT) as RU.
  pose proof HR as (_ & _ & _ & _ & _ & _ & [Bb Bh] & _).
  unfold decode_okb. cbv zeta.
  rewrite (proj2 (Z.leb_le 0 root)) by lia. rewrite (proj2 (Z.leb_le root 15)) by lia. cbn [andb].

  assert (I1 : forall h, 0 <= h -> 0 <= dec_idx1 root h < ctab_size p).
  { intros h Hh. unfold dec_idx1. pose proof (BITSv_range h root Hh ltac:(lia)). lia. }
  assert (N1 : forall h, 0 <= h -> 1 <= code_bits (code_at s p (dec_idx1 root h)) <= 15).
  { intros h Hh. unfold dec_idx1. pose proof (BITSv_range h root Hh ltac:(lia)).
    exact (proj1 (root_cell _ _ _ _ HT (BITSv h root) ltac:(lia))). }
  destruct (dchk_ok c 8 (dec_idx1 root) code_bits (ctab_size p) (code_at s p) r HR I1 N1 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
    as (r1 & E1 & HR1). rewrite E1.
  pose proof HR1 as (_ & _ & _ & _ & _ & _ & [Bb1 Bh1] & _).
  set (last := code_at s p (dec_idx1 root (ir_hold r1))).
  destruct (code_bits last <=? ir_bits r1) eqn:CB; [|reflexivity].
  destruct (two (code_op last)) eqn:TW; [|reflexivity]. cbn [andb].

  pose proof (BITSv_range (ir_hold r1) root ltac:(lia) ltac:(lia)) as XR.
  destruct (root_cell _ _ _ _ HT (BITSv (ir_hold r1) root) XR) as (Hbits & RL & RN).
  unfold dec_idx1 in last. fold last in Hbits, RL, RN.
  destruct (is_linkb last) eqn:HL.
  2:{ exfalso. destruct (RN eq_refl) as [_ SH]. exact (Hcontra last SH TW). }
  destruct (RL eq_refl) as (Hbr & Hop & Hv1 & Hv2).
  rewrite (proj2 (Z.leb_le _ 31)) by lia. cbn [andb].

  assert (I2 : forall h, 0 <= h -> 0 <= dec_idx2 last h < ctab_size p).
  { intros h Hh. unfold dec_idx2. rewrite BITSv_mod by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    pose proof (subidx_range h (code_bits last) (code_op last) ltac:(lia) ltac:(lia)). lia. }
  assert (N2 : forall h, 0 <= h -> 1 <= dec_need2 last (code_at s p (dec_idx2 last h)) <= 15).
  { intros h Hh. unfold dec_need2, dec_idx2. rewrite BITSv_mod by lia. rewrite Z.shiftr_div_pow2 by lia.
    pose proof (subidx_range h (code_bits last) (code_op last) ltac:(lia) ltac:(lia)) as Hy.
    destruct (sub_cell _ _ _ _ HT (BITSv (ir_hold r1) root) _ XR HL Hy) as (Sb & _ & _). fold last in Sb.
    rewrite wrap32_id by lia. lia. }
  destruct (dchk_ok c 8 (dec_idx2 last) (dec_need2 last) (ctab_size p) (code_at s p) r1 HR1 I2 N2 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
    as (r2 & E2 & _). rewrite E2. reflexivity.
Qed.

Lemma dists_two_contra : forall e,
  ((exists sy, 0 <= sy < nsyms DISTS /\ code_op e = fst (sym_entry DISTS sy) /\ code_val e = snd (sym_entry DISTS sy)) \/ code_op e = 64) ->
  dist_two (code_op e) = true -> False.
Proof.
  intros e SH TW. unfold dist_two in TW. apply Z.eqb_eq in TW.
  assert (NZ : code_op e <> 0).
  { destruct SH as [[sy (Hsy & Hop & Hv)]|Hop]; [|rewrite Hop; discriminate].
    cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L.
    destruct (sym_entry DISTS sy) as [op v]. cbn [fst snd] in Hop, Hv. rewrite Hop. destruct L as [(L & _)|[L _]]; lia. }
  exact (notlink_land240 DISTS e SH ltac:(discriminate) NZ TW).
Qed.

Definition len_two (op : Z) : bool := negb (op =? 0) && (Z.land op 240 =? 0).
Lemma lens_two_contra : forall e,
  ((exists sy, 0 <= sy < nsyms LENS /\ code_op e = fst (sym_entry LENS sy) /\ code_val e = snd (sym_entry LENS sy)) \/ code_op e = 64) ->
  len_two (code_op e) = true -> False.
Proof.
  intros e SH TW. unfold len_two in TW. apply andb_prop in TW as [T1 T2].
  apply Bool.negb_true_iff in T1. apply Z.eqb_neq in T1. apply Z.eqb_eq in T2.
  exact (notlink_land240 LENS e SH ltac:(discriminate) T1 T2).
Qed.

Theorem WINV_dist_okb : forall w, WINV w -> is_mode (w_s w) = DIST -> dist_okb w = true.
Proof.
  intros [s c r] HW E. unfold dist_okb. cbn [w_s w_c w_r] in *.
  unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (HC & HR & HMF & _).
  rewrite E in HMF. revert HMF. mred. intros (_ & _ & [_ HTD] & _).
  destruct (cpok_TBLg DISTS s (is_distcode s) (is_distbits s) HTD) as (used & HT & HU).
  apply (decode_okb_TBLg dist_two DISTS s c r _ _ used); try assumption.
  - discriminate.
  - destruct (is_distcode s); cbn [ctab_size]; lia.
  - exact dists_two_contra.
Qed.

Theorem WINV_len_decode_okb : forall w, WINV w -> (is_mode (w_s w) = LEN \/ is_mode (w_s w) = LEN_) ->
  decode_okb len_two (w_s w) (w_c w) (w_r w) (is_lencode (w_s w)) (is_lenbits (w_s w)) = true.
Proof.
  intros [s c r] HW E. cbn [w_s w_c w_r] in *.
  unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (HC & HR & HMF & _).
  assert (HTL : cpok LENS (is_codes s) (is_lencode s) (is_lenbits s)).
  { destruct E as [E|E]; rewrite E in HMF; revert HMF; mred; intros (_ & _ & [HTL _]); exact HTL. }
  destruct (cpok_TBLg LENS s (is_lencode s) (is_lenbits s) HTL) as (used & HT & HU).
  apply (decode_okb_TBLg len_two LENS s c r _ _ used); try assumption.
  - discriminate.
  - destruct (is_lencode s); cbn [ctab_size]; lia.
  - exact lens_two_contra.
Qed.


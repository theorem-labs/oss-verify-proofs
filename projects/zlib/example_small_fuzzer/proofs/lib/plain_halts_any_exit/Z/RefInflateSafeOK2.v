(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeF3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeFF.

Module RefInflateSafeOK.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
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


Theorem okL_of_WINV : forall (extra : Z -> iw -> bool) flush w,
  (forall w, WINV w -> is_mode (w_s w) <> DICT -> is_mode (w_s w) <> MEM -> is_mode (w_s w) <> SYNC -> extra flush w = true) ->
  WINV w ->
  (if (is_mode (w_s w) =? DICT) || (is_mode (w_s w) =? MEM) || (is_mode (w_s w) =? SYNC) then true
   else leave_okb (w_s w) && extra flush w) = true.
Proof.
  intros extra flush w HX HW.
  destruct (Z.eqb_spec (is_mode (w_s w)) DICT) as [E1|N1]; [reflexivity|].
  destruct (Z.eqb_spec (is_mode (w_s w)) MEM) as [E2|N2]; [reflexivity|].
  destruct (Z.eqb_spec (is_mode (w_s w)) SYNC) as [E3|N3]; [reflexivity|]. cbn [orb].
  rewrite (WINV_leave_okb w HW N1 N2). rewrite (HX w HW N1 N2 N3). reflexivity.
Qed.

End RefInflateSafeOK.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeFR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Strategy 100 [dodist dolen fast_trip inflate_fast NEEDBITS_k DECODE_k].

Lemma some_inj : forall {A} (a b : A), Some a = Some b -> a = b.
Proof. intros A a b H. injection H. intros E; exact E. Qed.


Theorem WINV_match_okb : forall w, WINV w -> is_mode (w_s w) = MATCH -> match_okb (w_s w) = true.
Proof.
  intros [s c r] HW E. unfold WINV in HW. cbn [w_s w_c w_r] in HW, E |- *. destruct HW as (_ & _ & HMF & _).
  rewrite E in HMF. revert HMF. mred. intros (_ & _ & _ & HL & HO). unfold match_okb.
  rewrite (proj2 (Z.leb_le 1 (is_length s))) by lia. rewrite (proj2 (Z.leb_le 1 (is_offset s))) by lia. reflexivity.
Qed.


Lemma WINV_LEN_ : forall s c r, WINV (mkW s c r) -> is_mode s = LEN_ -> WINV (mkW (iset_mode s LEN) c r).
Proof.
  intros s c r HW E. winv_open2 HW E HC HR. destruct HMF as (HCm & Hb8 & Htb).
  winv_split.
  - core_keep HC. apply CORE_length; exact HC.
  - exact HR.
  - split; [common_keep HCm|]. split; [left; exact Hb8|tables_keep Htb].
  - exact HWF.
  - exact HWB.
Qed.


Lemma distext_next_WINV : forall w w2, WINV w -> is_mode (w_s w) = DISTEXT -> distext_next w = Some w2 ->
  WINV w2 /\ is_mode (w_s w2) = MATCH.
Proof.
  intros [s c r] w2 HW E HN. unfold distext_next in HN. cbn [w_s w_c w_r] in HN, E.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HL & HX & HO). pose proof (CORE_length s HC) as HL0.
  destruct (Z.eqb_spec (is_extra s) 0) as [Cx|Cx].
  - apply some_inj in HN. subst w2. split; [|reflexivity].
    winv_split.
    + core_keep HC. exact HL0.
    + exact HR.
    + split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
    + exact HWF.
    + exact HWB.
  - destruct (NEEDBITS_spec c (is_extra s) s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)];
      rewrite EQ in HN; [|discriminate HN].
    apply some_inj in HN. subst w2. split; [|reflexivity].
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _).
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    unfold dx_s, dx_r.
    rewrite (BITSv_mod (ir_hold r1) (is_extra s)) by lia.
    pose proof (mod_pow2_range (ir_hold r1) (is_extra s) ltac:(lia)) as MV.
    pose proof (pow2_le (is_extra s) 15 ltac:(lia)) as P15.
    rewrite (wrap32_id (is_offset s + _)) by (change (2 ^ 15) with 32768 in P15; lia).
    rewrite (wrap32_id (ir_bits r1 - is_extra s)) by lia.
    winv_split.
    + core_keep HC. exact HL0.
    + apply REGS_holdbits; [exact HR1|]. apply HB_drop; [split; [exact RB1|exact RHO1]|lia].
    + split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. change (2 ^ 15) with 32768 in P15. lia.
    + rewrite Eo1. exact HWF.
    + rewrite Ep1. exact HWB.
Qed.

Theorem WINV_distext_chain : forall w, WINV w -> is_mode (w_s w) = DISTEXT -> distext_chain w = true.
Proof.
  intros w HW E. unfold distext_chain. rewrite (WINV_distext_okb w HW E).
  destruct (distext_next w) as [w2|] eqn:HN; [|reflexivity].
  destruct (distext_next_WINV w w2 HW E HN) as [HW2 E2]. exact (WINV_match_okb w2 HW2 E2).
Qed.


Lemma lenext_next_WINV : forall w w2, WINV w -> is_mode (w_s w) = LENEXT -> lenext_next w = Some w2 ->
  WINV w2 /\ is_mode (w_s w2) = DIST.
Proof.
  intros [s c r] w2 HW E HN. unfold lenext_next in HN. cbn [w_s w_c w_r] in HN, E.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HX & HL). pose proof (CORE_length s HC) as HL0.
  destruct (Z.eqb_spec (is_extra s) 0) as [Cx|Cx].
  - apply some_inj in HN. subst w2. split; [|reflexivity]. unfold lx_fin.
    winv_split.
    + core_keep HC. exact HL0.
    + exact HR.
    + split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
    + exact HWF.
    + exact HWB.
  - destruct (NEEDBITS_spec c (is_extra s) s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)];
      rewrite EQ in HN; [|discriminate HN].
    apply some_inj in HN. subst w2. split; [|reflexivity].
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _).
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    unfold lx_fin, lx_s, ddrop.
    rewrite (BITSv_mod (ir_hold r1) (is_extra s)) by lia.
    pose proof (mod_pow2_range (ir_hold r1) (is_extra s) ltac:(lia)) as MV.
    pose proof (pow2_le (is_extra s) 15 ltac:(lia)) as P15. change (2 ^ 15) with 32768 in P15.
    rewrite (wrap32_id (is_length s + _)) by lia.
    rewrite (wrap32_id (ir_bits r1 - is_extra s)) by lia.
    winv_split.
    + core_keep HC. lia.
    + apply REGS_holdbits; [exact HR1|]. apply HB_drop; [split; [exact RB1|exact RHO1]|lia].
    + split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
    + rewrite Eo1. exact HWF.
    + rewrite Ep1. exact HWB.
Qed.


Lemma table_next_WINV : forall w w2, WINV w -> is_mode (w_s w) = TABLE -> table_next w = Some w2 ->
  WINV w2 /\ is_mode (w_s w2) = LENLENS.
Proof.
  intros [s c r] w2 HW E HN. unfold table_next in HN. cbn [w_s w_c w_r] in HN, E.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb14].
  pose proof (CORE_length s HC) as HL0.
  destruct (NEEDBITS_spec c 14 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)];
    rewrite EQ in HN; [|discriminate HN].
  pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _).
  pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
  unfold tb_s2, tb_s, tb_r in HN. sacc_in HN.
  pose proof (mod_pow2_range (ir_hold r1) 5 ltac:(lia)) as M1.
  pose proof (mod_pow2_range (ir_hold r1) 10 ltac:(lia)) as M2.
  pose proof (mod_pow2_range (ir_hold r1) 14 ltac:(lia)) as M3.
  assert (D2 : 0 <= ir_hold r1 mod 2 ^ 10 / 2 ^ 5 < 32).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 5 * 32) with (2 ^ 10). lia. }
  assert (D3 : 0 <= ir_hold r1 mod 2 ^ 14 / 2 ^ 10 < 16).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 10 * 16) with (2 ^ 14). lia. }
  destruct (Z.ltb_spec 286 (ir_hold r1 mod 2 ^ 5 + 257)) as [C1|C1]; [discriminate HN|].
  destruct (Z.ltb_spec 30 (ir_hold r1 mod 2 ^ 10 / 2 ^ 5 + 1)) as [C2|C2]; [discriminate HN|]. cbn [orb] in HN.
  apply some_inj in HN. subst w2. split; [|reflexivity].
  winv_split.
  - core_keep HC. exact HL0.
  - apply REGS_holdbits; [exact HR1|]. apply HB_drop; [split; [exact RB1|exact RHO1]|lia].
  - split; [common_keep HCm|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    intros k Hk. exfalso. lia.
  - rewrite Eo1. exact HWF.
  - rewrite Ep1. exact HWB.
Qed.


Lemma dist_tailnext_WINV : forall s c here rt sb w2,
  CORE s -> REGS c rt -> common s -> tables s -> 1 <= is_length s ->
  ir_out rt = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put rt = 0) ->
  1 <= code_bits here <= ir_bits rt -> ir_bits rt - code_bits here < 8 ->
  ((exists sy, 0 <= sy < nsyms DISTS /\ code_op here = fst (sym_entry DISTS sy) /\ code_val here = snd (sym_entry DISTS sy)) \/ code_op here = 64) ->
  dist_tailnext s c here rt sb = Some w2 ->
  WINV w2 /\ is_mode (w_s w2) = DISTEXT.
Proof.
  intros s c here rt sb w2 HC HR HCm Htb HL HWF HWB Hcb Hb8 Hsh HN.
  pose proof HR as (_ & _ & _ & _ & _ & _ & [RB RHO] & _). pose proof (CORE_length s HC) as HL0.
  unfold dist_tailnext in HN.
  destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
  2:{ rewrite Hop in HN. cbn [Z.land Z.eqb negb] in HN. discriminate HN. }
  cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L.
  destruct (sym_entry DISTS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop, Hv in HN.
  destruct L as [(L1 & L2 & L3)|[L1 L2]].
  2:{ rewrite L1 in HN. cbn [Z.land Z.eqb negb] in HN. discriminate HN. }
  destruct (dist_op_facts op L1) as (F1 & F2 & F3 & F4). rewrite F2 in HN. cbn [Z.eqb negb] in HN.
  apply some_inj in HN. subst w2. split; [|reflexivity].
  rewrite F3. unfold dt_s, ddrop.
  pose proof (pow2_le (op - 16) 13 ltac:(lia)) as P13. change (2 ^ 13) with 8192 in P13.
  pose proof (pow2_pos (op - 16) ltac:(lia)) as P0.
  rewrite (wrap32_id (ir_bits rt - code_bits here)) by lia.
  winv_split.
  - core_keep HC. exact HL0.
  - apply REGS_holdbits; [exact HR|]. apply HB_drop; [split; [exact RB|exact RHO]|lia].
  - split; [common_keep HCm|]. split; [left; exact Hb8|]. split; [tables_keep Htb|]. lia.
  - exact HWF.
  - exact HWB.
Qed.

Lemma dist_next_WINV : forall w w2, WINV w -> is_mode (w_s w) = DIST -> dist_next w = Some w2 ->
  WINV w2 /\ is_mode (w_s w2) = DISTEXT.
Proof.
  intros [s c r] w2 HW E HN. unfold dist_next in HN. cbn [w_s w_c w_r] in HN, E.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HL).
  destruct (cpok_TBLg DISTS s (is_distcode s) (is_distbits s) (proj2 Htb)) as (used & HT & _).
  pose proof (T_root _ _ _ _ HT) as HR15.
  destruct (DECODE1_spec c s (is_distcode s) DISTS (is_distbits s) used HT r HR)
    as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)];
    rewrite EQ in HN; [|discriminate HN].
  pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _).
  pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
  destruct (root_cell DISTS _ _ used HT (ir_hold r1 mod 2 ^ is_distbits s) (ridx_range _ _ _ _ HT _)) as (Hbits & RLk & RNk).
  rewrite <- Eh in Hbits, RLk, RNk.
  assert (SAME : ir_bits r1 = ir_bits r -> ir_hold r1 = ir_hold r).
  { intros Eb. destruct HP1 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
  destruct (dist_two (code_op here)) eqn:Clink.
  -
    unfold dist_two in Clink. apply Z.eqb_eq in Clink.
    assert (HLk : is_linkb here = true).
    { destruct (is_linkb here) eqn:Lk; [reflexivity|]. exfalso. destruct (RNk eq_refl) as [_ SH].
      apply (notlink_land240 DISTS here SH ltac:(discriminate)); [|exact Clink].
      destruct SH as [[sy (Hsy & Hop & _)]|Hop]; [|rewrite Hop; discriminate].
      cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L. destruct (sym_entry DISTS sy) as [op v]. cbn [fst] in Hop. rewrite Hop. lia. }
    destruct (RLk HLk) as (Hbr & Hop & Hv1 & Hv2).
    destruct (DECODE2_spec c s (is_distcode s) DISTS (is_distbits s) used HT r1 here HR1 Eh HLk Hle)
      as [(r2 & here2 & EQ2 & HR2 & HP2 & Eh2 & Hsb & Hle2 & Hb2)|(r2 & EQ2 & HR2 & HP2 & Hh2 & Hb2)];
      rewrite EQ2 in HN; [|discriminate HN].
    pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & El2 & _).
    pose proof HR2 as (_ & _ & _ & _ & _ & _ & [RB2 RHO2] & _).
    pose proof (sub_cell DISTS _ _ used HT (ir_hold r1 mod 2 ^ is_distbits s)
                  (ir_hold r2 mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here)) as SC.
    rewrite <- Eh in SC.
    specialize (SC (ridx_range _ _ _ _ HT _) HLk (subidx_range (ir_hold r2) (code_bits here) (code_op here) ltac:(lia) ltac:(lia))).
    unfold subix in Eh2. rewrite <- Eh2 in SC. destruct SC as (Sb & SNL & SN).
    assert (SAME2 : ir_bits r2 = ir_bits r1 -> ir_hold r2 = ir_hold r1).
    { intros Eb. destruct HP2 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
    assert (B8 : ir_bits r2 - code_bits here - code_bits here2 < 8).
    { destruct Hb2 as [Hb2|Hb2]; [|lia]. destruct Hb1 as [Hb1|Hb1]; [|lia].
      destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
      rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
      rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. rewrite (SAME2 Hb2) in Eh2. rewrite <- Eh2 in Hbx. lia. }
    unfold ddrop in HN. sacc_in HN. rewrite (wrap32_id (ir_bits r2 - code_bits here)) in HN by lia.
    eapply (dist_tailnext_WINV s c here2 _ _ w2 HC); try exact HN;
      first [ apply REGS_holdbits; [exact HR2|]; apply HB_drop; [split; [exact RB2|exact RHO2]|lia]
            | exact HCm | exact Htb | exact HL
            | sacc; rewrite Eo2, Eo1; exact HWF
            | sacc; rewrite Ep2, Ep1; exact HWB
            | sacc; lia
            | exact SN ].
  -
    assert (HLk : is_linkb here = false).
    { destruct (is_linkb here) eqn:Lk; [|reflexivity]. exfalso. destruct (RLk eq_refl) as (_ & Hop & _).
      unfold dist_two in Clink. rewrite (land240_small (code_op here)) in Clink by lia. discriminate Clink. }
    destruct (RNk HLk) as [Hbr SH].
    assert (B8 : ir_bits r1 - code_bits here < 8).
    { destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
      rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
      rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. lia. }
    eapply (dist_tailnext_WINV s c here r1 _ w2 HC HR1 HCm Htb HL); try exact HN;
      first [ rewrite Eo1; exact HWF | rewrite Ep1; exact HWB | lia | exact SH ].
Qed.

Theorem WINV_dist_chain : forall w, WINV w -> is_mode (w_s w) = DIST -> dist_chain w = true.
Proof.
  intros w HW E. unfold dist_chain. rewrite (WINV_dist_okb w HW E).
  destruct (dist_next w) as [w2|] eqn:HN; [|reflexivity].
  destruct (dist_next_WINV w w2 HW E HN) as [HW2 E2]. exact (WINV_distext_chain w2 HW2 E2).
Qed.

Theorem WINV_lenext_chain : forall w, WINV w -> is_mode (w_s w) = LENEXT -> lenext_chain w = true.
Proof.
  intros w HW E. unfold lenext_chain. rewrite (WINV_lenext_okb w HW E).
  destruct (lenext_next w) as [w2|] eqn:HN; [|reflexivity].
  destruct (lenext_next_WINV w w2 HW E HN) as [HW2 E2]. exact (WINV_dist_chain w2 HW2 E2).
Qed.


Lemma len_tailnext_WINV : forall c here rt sb w2,
  CORE sb -> REGS c rt -> common sb -> tables sb ->
  ir_out rt = arr_len (ic_outbuf c) -> (is_wbits sb = 0 -> ir_put rt = 0) ->
  1 <= code_bits here <= ir_bits rt -> ir_bits rt - code_bits here < 8 ->
  ((exists sy, 0 <= sy < nsyms LENS /\ code_op here = fst (sym_entry LENS sy) /\ code_val here = snd (sym_entry LENS sy)) \/ code_op here = 64) ->
  len_tailnext c here rt sb = Some w2 ->
  WINV w2 /\ is_mode (w_s w2) = LENEXT.
Proof.
  intros c here rt sb w2 HC HR HCm Htb HWF HWB Hcb Hb8 Hsh HN.
  pose proof HR as (_ & _ & _ & _ & _ & _ & [RB RHO] & _). pose proof (CORE_length sb HC) as HL0.
  unfold len_tailnext in HN. cbv zeta in HN.
  destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
  2:{ rewrite Hop in HN. cbn [Z.land Z.eqb negb orb] in HN. discriminate HN. }
  cbn [nsyms] in Hsy. pose proof (lens_sym_cases sy Hsy) as L.
  destruct (sym_entry LENS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop, Hv in HN.
  destruct L as [[L1 L2]|[[L1 L2]|[(L1 & L2 & L3)|[L1|L1]]]];
    try (rewrite L1 in HN; cbn [Z.land Z.eqb negb orb] in HN; discriminate HN).
  destruct (len_op_facts op L1) as (F1 & F2 & F3 & F4 & F5).
  replace (op =? 0) with false in HN by (symmetry; apply Z.eqb_neq; lia).
  rewrite F5, F2 in HN. cbn [Z.eqb negb orb] in HN.
  apply some_inj in HN. subst w2. split; [|reflexivity].
  rewrite F3. unfold addback, ddrop.
  pose proof (pow2_pos (op - 16) ltac:(lia)) as P0.
  rewrite (wrap32_id (ir_bits rt - code_bits here)) by lia.
  winv_split.
  - core_keep HC. lia.
  - apply REGS_holdbits; [exact HR|]. apply HB_drop; [split; [exact RB|exact RHO]|lia].
  - split; [common_keep HCm|]. split; [left; exact Hb8|]. split; [tables_keep Htb|]. lia.
  - exact HWF.
  - exact HWB.
Qed.

Lemma len_next_WINV : forall w w2, WINV w -> is_mode (w_s w) = LEN -> len_next w = Some w2 ->
  WINV w2 /\ is_mode (w_s w2) = LENEXT.
Proof.
  intros [s c r] w2 HW E HN. unfold len_next in HN. cbn [w_s w_c w_r] in HN, E.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb).
  destruct ((6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)); [discriminate HN|].
  cbv zeta in HN.
  assert (HC0 : CORE (iset_back s 0)) by (core_keep HC; apply CORE_length; exact HC).
  assert (HCm0 : common (iset_back s 0)) by (common_keep HCm).
  assert (Htb0 : tables (iset_back s 0)) by (tables_keep Htb).
  assert (HWB0 : is_wbits (iset_back s 0) = 0 -> ir_put r = 0) by (sacc; exact HWB).
  destruct (cpok_TBLg LENS s (is_lencode s) (is_lenbits s) (proj1 Htb)) as (used & HT' & _).
  assert (HT : TBLg LENS (code_at (iset_back s 0) (is_lencode s)) (is_lenbits s) used) by exact HT'.
  pose proof (T_root _ _ _ _ HT) as HR15.
  destruct (DECODE1_spec c (iset_back s 0) (is_lencode s) LENS (is_lenbits s) used HT r HR)
    as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)];
    rewrite EQ in HN; [|discriminate HN].
  pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _).
  pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
  destruct (root_cell LENS _ _ used HT (ir_hold r1 mod 2 ^ is_lenbits s) (ridx_range _ _ _ _ HT _)) as (Hbits & RLk & RNk).
  rewrite <- Eh in Hbits, RLk, RNk.
  assert (SAME : ir_bits r1 = ir_bits r -> ir_hold r1 = ir_hold r).
  { intros Eb. destruct HP1 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
  assert (Hbx' : ir_bits r < 8 \/ ir_bits r < lneedg (code_at (iset_back s 0) (is_lencode s)) (is_lenbits s) (ir_hold r)).
  { rewrite <- lneed_lneedg. rewrite (lneed_keep s (iset_back s 0)) by reflexivity. exact Hbx. }
  destruct (RefInflateOkb.len_two (code_op here)) eqn:Clink.
  -
    unfold RefInflateOkb.len_two in Clink. apply andb_prop in Clink as [Cnz Clink]. apply Z.eqb_eq in Clink.
    apply Bool.negb_true_iff in Cnz. apply Z.eqb_neq in Cnz.
    assert (HLk : is_linkb here = true).
    { destruct (is_linkb here) eqn:Lk; [reflexivity|]. exfalso. destruct (RNk eq_refl) as [_ SH].
      exact (notlink_land240 LENS here SH ltac:(discriminate) Cnz Clink). }
    destruct (RLk HLk) as (Hbr & Hop & Hv1 & Hv2).
    destruct (DECODE2_spec c (iset_back s 0) (is_lencode s) LENS (is_lenbits s) used HT r1 here HR1 Eh HLk Hle)
      as [(r2 & here2 & EQ2 & HR2 & HP2 & Eh2 & Hsb & Hle2 & Hb2)|(r2 & EQ2 & HR2 & HP2 & Hh2 & Hb2)];
      rewrite EQ2 in HN; [|discriminate HN].
    pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & El2 & _).
    pose proof HR2 as (_ & _ & _ & _ & _ & _ & [RB2 RHO2] & _).
    pose proof (sub_cell LENS _ _ used HT (ir_hold r1 mod 2 ^ is_lenbits s)
                  (ir_hold r2 mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here)) as SC.
    rewrite <- Eh in SC.
    specialize (SC (ridx_range _ _ _ _ HT _) HLk (subidx_range (ir_hold r2) (code_bits here) (code_op here) ltac:(lia) ltac:(lia))).
    unfold subix in Eh2. rewrite <- Eh2 in SC. destruct SC as (Sb & SNL & SN).
    assert (SAME2 : ir_bits r2 = ir_bits r1 -> ir_hold r2 = ir_hold r1).
    { intros Eb. destruct HP2 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
    assert (B8 : ir_bits r2 - code_bits here - code_bits here2 < 8).
    { destruct Hb2 as [Hb2|Hb2]; [|lia]. destruct Hb1 as [Hb1|Hb1]; [|lia].
      destruct Hbx' as [Hbx'|Hbx']; [lia|]. exfalso.
      unfold lneedg in Hbx'.
      rewrite <- (SAME Hb1), <- Eh, HLk in Hbx'. rewrite (SAME2 Hb2) in Eh2. rewrite <- Eh2 in Hbx'. lia. }
    unfold ddrop in HN. sacc_in HN. rewrite (wrap32_id (ir_bits r2 - code_bits here)) in HN by lia.
    eapply (len_tailnext_WINV c here2 _ _ w2); try exact HN;
      first [ unfold addback; core_keep HC; apply CORE_length; exact HC
            | apply REGS_holdbits; [exact HR2|]; apply HB_drop; [split; [exact RB2|exact RHO2]|lia]
            | unfold addback; common_keep HCm
            | unfold addback; tables_keep Htb
            | sacc; rewrite Eo2, Eo1; exact HWF
            | unfold addback; sacc; rewrite Ep2, Ep1; exact HWB
            | sacc; lia
            | exact SN ].
  -
    assert (HLk : is_linkb here = false).
    { destruct (is_linkb here) eqn:Lk; [|reflexivity]. exfalso. destruct (RLk eq_refl) as (_ & Hop & _).
      unfold RefInflateOkb.len_two in Clink. rewrite (land240_small (code_op here)) in Clink by lia.
      replace (code_op here =? 0) with false in Clink by (symmetry; apply Z.eqb_neq; lia). discriminate Clink. }
    destruct (RNk HLk) as [Hbr SH].
    assert (B8 : ir_bits r1 - code_bits here < 8).
    { destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct Hbx' as [Hbx'|Hbx']; [lia|]. exfalso.
      unfold lneedg in Hbx'. rewrite <- (SAME Hb1), <- Eh, HLk in Hbx'. lia. }
    eapply (len_tailnext_WINV c here r1 _ w2 HC0 HR1 HCm0 Htb0); try exact HN;
      first [ rewrite Eo1; exact HWF | rewrite Ep1; exact HWB0 | lia | exact SH ].
Qed.


Lemma tables_roots : forall s, tables s -> 0 <= is_lenbits s <= 15 /\ 0 <= is_distbits s <= 15.
Proof.
  intros s [HL HD].
  destruct (cpok_TBLg LENS s _ _ HL) as (u1 & T1 & _). destruct (cpok_TBLg DISTS s _ _ HD) as (u2 & T2 & _).
  pose proof (T_root _ _ _ _ T1). pose proof (T_root _ _ _ _ T2). lia.
Qed.

Lemma inflate_fast_input : forall s c r, ic_input (w_c (inflate_fast (mkW s c r))) = ic_input c.
Proof.
  intros s c r. unfold inflate_fast. cbn [w_s w_c w_r]. cbv zeta.
  lazymatch goal with |- context [iterZ ?n ?st ?d ?a] => generalize (iterZ n st d a); intros [f mm] end.
  destruct mm as [[md [mg|]]|]; cbn [w_c]; destruct c; reflexivity.
Qed.

Lemma WINV_lenfast_okb : forall s c r, WINV (mkW s c r) -> is_mode s = LEN -> 6 <= ir_have r -> 258 <= ir_left r ->
  lenfast_okb (mkW s c r) = true.
Proof.
  intros s c r HW E H6 H258. unfold lenfast_okb. cbv zeta. cbn [w_c].
  rewrite (ff_ok_LEN s c r HW E H6 H258). cbn [andb].
  pose proof (inflate_fast_post (mkW s c r) s c r HW E H6 H258 (Z.le_refl _)) as P.
  cbv beta iota delta [abind amodify gs aret] in P.
  set (w1 := inflate_fast (RESTORE (mkW s c r))) in *.
  assert (CUR : 0 <= ic_next_in (w_c w1) /\ 0 <= ic_avail_in (w_c w1) /\ ic_next_in (w_c w1) + ic_avail_in (w_c w1) = arr_len (ic_input (w_c w1))
                /\ 0 <= ic_next_out (w_c w1) /\ 0 <= ic_avail_out (w_c w1) /\ ic_next_out (w_c w1) + ic_avail_out (w_c w1) = arr_len (ic_outbuf (w_c w1))).
  { unfold LOAD, wset_r in P. cbn [w_s] in P.
    destruct (is_mode (w_s w1) =? TYPE); cbv beta iota in P; [rewrite set_back_ref in P|]; cbn [POST] in P; destruct P as [HW1 _];
      unfold WINV in HW1; cbn [w_s w_c w_r] in HW1; destruct HW1 as (_ & HR1 & _); unfold REGS in HR1;
      cbn [ir_next ir_have ir_put ir_left] in HR1; destruct HR1 as (A1 & A2 & A3 & A4 & A5 & A6 & _);
      repeat split; assumption. }
  assert (EI : ic_input (w_c w1) = ic_input c).
  { subst w1. unfold RESTORE. cbn [w_s w_c w_r]. rewrite inflate_fast_input. destruct c; reflexivity. }
  assert (EO : arr_len (ic_outbuf (w_c w1)) = arr_len (ic_outbuf c)).
  { subst w1. unfold RESTORE. cbn [w_s w_c w_r].
    lazymatch goal with |- arr_len (ic_outbuf (w_c (inflate_fast (mkW ?s1 ?c1 ?r1)))) = _ =>
      destruct (inflate_fast_frame_proof s1 c1 r1) as (_ & X & _); rewrite X end.
    destruct c; reflexivity. }
  rewrite EI, EO in CUR. destruct CUR as (A1 & A2 & A3 & A4 & A5 & A6).
  rewrite (proj2 (Z.leb_le _ _) A1), (proj2 (Z.leb_le _ _) A2), (proj2 (Z.eqb_eq _ _) A3).
  rewrite (proj2 (Z.leb_le _ _) A4), (proj2 (Z.leb_le _ _) A5), (proj2 (Z.eqb_eq _ _) A6). reflexivity.
Qed.

Theorem WINV_len_okb : forall w, WINV w -> is_mode (w_s w) = LEN -> len_okb w = true.
Proof.
  intros [s c r] HW E. cbn [w_s] in E. unfold len_okb. cbn [w_s w_c w_r].
  pose proof HW as HW0. winv_open2 HW E HC HR. destruct HMF as (HCm & Hbx & Htb).
  pose proof (tables_roots s Htb) as [RL RD].
  rewrite (proj2 (Z.leb_le 0 (is_lenbits s))), (proj2 (Z.leb_le (is_lenbits s) 15)) by lia.
  rewrite (proj2 (Z.leb_le 0 (is_distbits s))), (proj2 (Z.leb_le (is_distbits s) 15)) by lia. cbn [andb].
  destruct (Z.leb_spec 6 (ir_have r)) as [H6|H6]; destruct (Z.leb_spec 258 (ir_left r)) as [H258|H258]; cbn [andb].
  - (* zlib 1.4: the fast case also splits on bits < 8 *)
    destruct (Z.ltb_spec (ir_bits r) 8) as [H8|H8].
    + exact (WINV_lenfast_okb s c r HW0 E H6 H258).
    + change RefInflateOkb.len_two with RefInflateSafeOK.len_two. exact (WINV_len_decode_okb (mkW s c r) HW0 (or_introl E)).
  - change RefInflateOkb.len_two with RefInflateSafeOK.len_two. exact (WINV_len_decode_okb (mkW s c r) HW0 (or_introl E)).
  - change RefInflateOkb.len_two with RefInflateSafeOK.len_two. exact (WINV_len_decode_okb (mkW s c r) HW0 (or_introl E)).
  - change RefInflateOkb.len_two with RefInflateSafeOK.len_two. exact (WINV_len_decode_okb (mkW s c r) HW0 (or_introl E)).
Qed.

Theorem WINV_len_chain : forall w, WINV w -> is_mode (w_s w) = LEN -> len_chain w = true.
Proof.
  intros w HW E. unfold len_chain. rewrite (WINV_len_okb w HW E).
  destruct (len_next w) as [w2|] eqn:HN; [|reflexivity].
  destruct (len_next_WINV w w2 HW E HN) as [HW2 E2]. exact (WINV_lenext_chain w2 HW2 E2).
Qed.

Theorem WINV_len__chain : forall w, WINV w -> is_mode (w_s w) = LEN_ -> len__chain w = true.
Proof.
  intros [s c r] HW E. cbn [w_s] in E. unfold len__chain. cbn [w_s w_c w_r].
  apply WINV_len_chain; [exact (WINV_LEN_ s c r HW E) | reflexivity].
Qed.

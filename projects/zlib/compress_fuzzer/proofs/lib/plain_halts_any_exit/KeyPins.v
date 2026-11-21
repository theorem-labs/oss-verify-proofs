(** * KeyPins — the pins conjunct of B3, from the ent tie clause


    g1's fused B3 heads conclude [... /\ zr_len_ents lit ent] (resp.
    [zr_dist_ents dst ent]) at the witness tied by
    [ent sym = ZReproQ6K.it_entry cL (Z.of_nat sym) (c_bits (ent sym))].
    Given the tie, the pins are VALUE facts about [it_entry] over the
    build ctx's base/extra arrays — no canonical-code content ([code_for]
    only selects coded syms and bounds them by the list length).  This
    file: the [it_pre] PreGo ctx shape, the base/extra vm bridges (over
    the [mkCodeT] projections, absorbing the u8/u16 casts), and the two
    pins lemmas.  Generic in the lens list per g1's seam flag (NEVER
    instantiated at lit ++ dst). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Huff DeflateSpec Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6F ZReproQ6K.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6P.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The PreGo ctx shape: base/extra/match are type-pinned.
   ========================================================================== *)

Lemma it_pre_go_ctx : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  x_match c = (if Z.eqb ty CT_LENS then 257
               else if Z.eqb ty CT_DISTS then 0 else 20)
  /\ x_base c = (if Z.eqb ty CT_LENS then lbase
                 else if Z.eqb ty CT_DISTS then dbase else x_work c)
  /\ x_extra c = (if Z.eqb ty CT_LENS then lext
                  else if Z.eqb ty CT_DISTS then dext else x_work c).
Proof.
  intros ty lens codes root0 t0 c st H.
  revert H. unfold it_pre. cbv zeta.
  set (cnt := it_count (Z.to_nat codes) 0 lens zzero).
  set (mx := it_findmax 15%nat MAXBITS cnt).
  set (wk := snd (it_sort (Z.to_nat codes) 0 lens
                    (it_offs 14%nat 1 cnt (zset zzero 1 0)) zzero)).
  destruct (Z.eqb mx 0); [intros H; discriminate|].
  destruct (it_kraft 15%nat 1 1 cnt) as [lft|]; [|intros H; discriminate].
  destruct (it_incomplete ty lft mx); [intros H; discriminate|].
  match goal with
  | |- context [if it_enough ?a ?b then _ else _] =>
      destruct (it_enough a b)
  end; [intros H; discriminate|].
  intros H. injection H as <- _.
  repeat split; reflexivity.
Qed.

(* ==========================================================================
   2.  The base/extra vm bridges, stated over the [mkCodeT] projections
       so the u8/u16 casts are inside the checked values.
   ========================================================================== *)

Definition len_pin_ok (w : nat) : bool :=
  match nth_error length_base w, nth_error length_extra w with
  | Some b0, Some e0 =>
      let e := mkCodeT (lext (Z.of_nat w)) 0 (lbase (Z.of_nat w)) in
      (c_op e =? 16 + Z.of_nat e0)
      && (Z.land (c_op e) 32 =? 0)
      && (Z.land (c_op e) 64 =? 0)
      && (Z.land (c_op e) 15 =? Z.of_nat e0)
      && (c_val e =? Z.of_nat b0)
      && (3 <=? b0)%nat && (b0 <=? 258)%nat && (e0 <=? 5)%nat
      && (b0 + 2 ^ e0 - 1 <=? 258)%nat
  | _, _ => false
  end.

Lemma len_pins_chk : forallb len_pin_ok (seq 0 29) = true.
Proof. vm_compute. reflexivity. Qed.

Definition dist_pin_ok (w : nat) : bool :=
  match nth_error dist_base w, nth_error dist_extra w with
  | Some b0, Some e0 =>
      let e := mkCodeT (dext (Z.of_nat w)) 0 (dbase (Z.of_nat w)) in
      (c_op e =? 16 + Z.of_nat e0)
      && (Z.land (c_op e) 64 =? 0)
      && (Z.land (c_op e) 15 =? Z.of_nat e0)
      && (c_val e =? Z.of_nat b0)
      && (1 <=? Z.of_nat b0) && (Z.of_nat b0 <=? 32768)
      && (e0 <=? 13)%nat
  | _, _ => false
  end.

Lemma dist_pins_chk : forallb dist_pin_ok (seq 0 30) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma forallb_seq_at : forall f n k,
  forallb f (seq 0 n) = true -> (k < n)%nat -> f k = true.
Proof.
  intros f n k H Hk.
  rewrite forallb_forall in H. apply H, in_seq. lia.
Qed.

(** The projections of [mkCodeT] ignore the bits argument, so the
    checker's b=0 instance speaks for every bits value. *)
Lemma mkCodeT_op_bits : forall op b b' v,
  c_op (mkCodeT op b v) = c_op (mkCodeT op b' v).
Proof. reflexivity. Qed.

Lemma mkCodeT_val_bits : forall op b b' v,
  c_val (mkCodeT op b v) = c_val (mkCodeT op b' v).
Proof. reflexivity. Qed.

(* ==========================================================================
   3.  Coded symbols are in range.
   ========================================================================== *)

Lemma code_for_sym_lt : forall (L : list nat) (sym : nat) cw,
  code_for L 15%nat sym = Some cw -> (sym < length L)%nat.
Proof.
  intros L sym cw H. unfold code_for in H.
  destruct (nth_error L sym) eqn:E; [|discriminate].
  apply nth_error_Some. rewrite E. discriminate.
Qed.

(* ==========================================================================
   4.  The pins lemmas.
   ========================================================================== *)

Theorem zr_len_ents_of_tie :
  forall (cL : ItCtx) lens codes root0 t0 stL (ll : list nat)
         (ent : nat -> Code),
    it_pre CT_LENS lens codes root0 t0 = PreGo cL stL ->
    (length ll <= 286)%nat ->
    (forall sym, ent sym = it_entry cL (Z.of_nat sym) (c_bits (ent sym))) ->
    ZReproQ6P.zr_len_ents ll ent.
Proof.
  intros cL lens codes root0 t0 stL ll ent Hpre Hlen Htie.
  destruct (it_pre_go_ctx _ _ _ _ _ _ _ Hpre) as (Hm & Hb & He).
  assert (HmL : x_match cL = 257) by (rewrite Hm; reflexivity).
  assert (HbL : x_base cL = lbase) by (rewrite Hb; reflexivity).
  assert (HeL : x_extra cL = lext) by (rewrite He; reflexivity).
  intros sym cw Hcf.
  pose proof (code_for_sym_lt _ _ _ Hcf) as Hsym.
  rewrite (Htie sym). unfold it_entry.
  rewrite HmL, HbL, HeL.
  destruct (Nat.lt_ge_cases sym 256) as [Hlt | Hge].
  - (* literal arm: op = u8 0 = 0, val = u16 sym = sym *)
    left.
    destruct (Z.ltb_spec (Z.of_nat sym + 1) 257); [|lia].
    cbn [mkCodeT c_op c_val].
    split; [exact Hlt|].
    split; [reflexivity|].
    apply u16_id. lia.
  - destruct (Nat.eq_dec sym 256) as [-> | Hne].
    + (* EOB arm: 96 marker *)
      right; left.
      destruct (Z.ltb_spec (Z.of_nat 256 + 1) 257); [lia|].
      destruct (Z.leb_spec 257 (Z.of_nat 256)); [lia|].
      cbn [mkCodeT c_op c_val].
      split; [reflexivity|].
      repeat split; cbv; discriminate || reflexivity.
    + (* length-symbol arm *)
      right; right; left.
      assert (H257 : (257 <= sym)%nat) by lia.
      destruct (Z.ltb_spec (Z.of_nat sym + 1) 257); [lia|].
      destruct (Z.leb_spec 257 (Z.of_nat sym)); [|lia].
      assert (Hw : (sym - 257 < 29)%nat) by lia.
      pose proof (forallb_seq_at _ _ _ len_pins_chk Hw) as Hpin.
      unfold len_pin_ok in Hpin.
      destruct (nth_error length_base (sym - 257)%nat) as [b0|] eqn:Eb;
        [|discriminate].
      destruct (nth_error length_extra (sym - 257)%nat) as [e0|] eqn:Ee;
        [|discriminate].
      cbv zeta in Hpin.
      repeat (apply andb_prop in Hpin as [Hpin ?]).
      repeat match goal with
      | H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H
      | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
      | H : (_ <=? _)%nat = true |- _ => apply Nat.leb_le in H
      end.
      split; [exact H257|].
      exists b0, e0.
      replace (Z.of_nat sym - 257) with (Z.of_nat (sym - 257)%nat) by lia.
      rewrite (mkCodeT_op_bits (lext (Z.of_nat (sym - 257)%nat))
                 (c_bits (ent sym)) 0
                 (lbase (Z.of_nat (sym - 257)%nat))).
      rewrite (mkCodeT_val_bits (lext (Z.of_nat (sym - 257)%nat))
                 (c_bits (ent sym)) 0
                 (lbase (Z.of_nat (sym - 257)%nat))).
      repeat split; try assumption; try congruence; try lia.
Qed.

Theorem zr_dist_ents_of_tie :
  forall (cD : ItCtx) lens codes root0 t0 stD (dl : list nat)
         (ent : nat -> Code),
    it_pre CT_DISTS lens codes root0 t0 = PreGo cD stD ->
    (length dl <= 30)%nat ->
    (forall sym, ent sym = it_entry cD (Z.of_nat sym) (c_bits (ent sym))) ->
    ZReproQ6P.zr_dist_ents dl ent.
Proof.
  intros cD lens codes root0 t0 stD dl ent Hpre Hlen Htie.
  destruct (it_pre_go_ctx _ _ _ _ _ _ _ Hpre) as (Hm & Hb & He).
  assert (HmD : x_match cD = 0) by (rewrite Hm; reflexivity).
  assert (HbD : x_base cD = dbase) by (rewrite Hb; reflexivity).
  assert (HeD : x_extra cD = dext) by (rewrite He; reflexivity).
  intros sym cw Hcf.
  pose proof (code_for_sym_lt _ _ _ Hcf) as Hsym.
  rewrite (Htie sym). unfold it_entry.
  rewrite HmD, HbD, HeD.
  left.
  destruct (Z.ltb_spec (Z.of_nat sym + 1) 0); [lia|].
  destruct (Z.leb_spec 0 (Z.of_nat sym)); [|lia].
  assert (Hw : (sym < 30)%nat) by lia.
  pose proof (forallb_seq_at _ _ _ dist_pins_chk Hw) as Hpin.
  unfold dist_pin_ok in Hpin.
  destruct (nth_error dist_base sym) as [b0|] eqn:Eb; [|discriminate].
  destruct (nth_error dist_extra sym) as [e0|] eqn:Ee; [|discriminate].
  cbv zeta in Hpin.
  repeat (apply andb_prop in Hpin as [Hpin ?]).
  repeat match goal with
  | H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H
  | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _)%nat = true |- _ => apply Nat.leb_le in H
  end.
  exists b0, e0.
  replace (Z.of_nat sym - 0) with (Z.of_nat sym) by lia.
  rewrite (mkCodeT_op_bits (dext (Z.of_nat sym)) (c_bits (ent sym)) 0
             (dbase (Z.of_nat sym))).
  rewrite (mkCodeT_val_bits (dext (Z.of_nat sym)) (c_bits (ent sym)) 0
             (dbase (Z.of_nat sym))).
  repeat split; try assumption; try congruence; try lia.
Qed.

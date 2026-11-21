(** * Gap7Ents — TIGHT ent-pack variants for the ZrBodySelect proof.

    OWNER: an earlier development run (GAP7 Route B; the ruling's sanctioned DUPLICATION
    FALLBACK for sibling gap (ii) — q4's export offer stands and either
    artifact serves; receipts make a later swap mechanical).

    The landed producers (KeyPins.zr_{len,dist}_ents_of_tie) never
    inhabit the invalid arms of ZReproQ6P.zr_{len,dist}_ents — measured
    in their proof bodies (len: left / right;left / right;right;left
    only; dist: left only).  These are the SAME theorems at the SAME
    premises concluding the TIGHT Props (invalid arms dropped), proof
    bodies verbatim from the landed KeyPins modulo ONE arm-selector
    hunk each.  The trip's LEN/DIST arm kills consume the tight Props:
    a coded symbol's entry can never carry op&64.

    Prop texts: arms verbatim from ZReproQ6P.zr_len_ents (arms 1-3) /
    zr_dist_ents (coded arm).

    PA-EXPORTS: zr_len_ents3_of_tie, zr_dist_ents1_of_tie.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Huff DeflateSpec Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6F ZReproQ6K KeyPins.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6P.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Definition zr_len_ents3 (ll : list nat) (entl : nat -> Code) : Prop :=
  forall sym cw, code_for ll 15%nat sym = Some cw ->
    ((sym < 256)%nat /\ c_op (entl sym) = 0
       /\ c_val (entl sym) = Z.of_nat sym)
    \/ (sym = 256%nat /\ c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 <> 0
        /\ Z.land (c_op (entl sym)) 16 = 0
        /\ Z.land (c_op (entl sym)) 64 <> 0)
    \/ ((257 <= sym)%nat
        /\ exists b0 e0,
             nth_error length_base (sym - 257)%nat = Some b0
             /\ nth_error length_extra (sym - 257)%nat = Some e0
             /\ c_op (entl sym) = 16 + Z.of_nat e0
             /\ Z.land (c_op (entl sym)) 32 = 0
             /\ Z.land (c_op (entl sym)) 64 = 0
             /\ Z.land (c_op (entl sym)) 15 = Z.of_nat e0
             /\ c_val (entl sym) = Z.of_nat b0
             /\ (3 <= b0)%nat /\ (b0 <= 258)%nat /\ (e0 <= 5)%nat
             /\ (b0 + 2 ^ e0 - 1 <= 258)%nat).

Definition zr_dist_ents1 (dl : list nat) (entd : nat -> Code) : Prop :=
  forall sym cw, code_for dl 15%nat sym = Some cw ->
    exists b0 e0,
      nth_error dist_base sym = Some b0
      /\ nth_error dist_extra sym = Some e0
      /\ c_op (entd sym) = 16 + Z.of_nat e0
      /\ Z.land (c_op (entd sym)) 64 = 0
      /\ Z.land (c_op (entd sym)) 15 = Z.of_nat e0
      /\ c_val (entd sym) = Z.of_nat b0
      /\ 1 <= Z.of_nat b0 <= 32768 /\ (e0 <= 13)%nat.

Theorem zr_len_ents3_of_tie :
  forall (cL : ItCtx) lens codes root0 t0 stL (ll : list nat)
         (ent : nat -> Code),
    it_pre CT_LENS lens codes root0 t0 = PreGo cL stL ->
    (length ll <= 286)%nat ->
    (forall sym, ent sym = it_entry cL (Z.of_nat sym) (c_bits (ent sym))) ->
    zr_len_ents3 ll ent.
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
      right; right.
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

Theorem zr_dist_ents1_of_tie :
  forall (cD : ItCtx) lens codes root0 t0 stD (dl : list nat)
         (ent : nat -> Code),
    it_pre CT_DISTS lens codes root0 t0 = PreGo cD stD ->
    (length dl <= 30)%nat ->
    (forall sym, ent sym = it_entry cD (Z.of_nat sym) (c_bits (ent sym))) ->
    zr_dist_ents1 dl ent.
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

Set Printing Width 2000.
Print Assumptions zr_len_ents3_of_tie.
Print Assumptions zr_dist_ents1_of_tie.

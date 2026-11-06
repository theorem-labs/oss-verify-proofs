(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hex_byte_ok (s : string) (o : int) : bool :=
  match hex_byte s o with Some _ => true | None => false end.

Fixpoint hex_ok_pos (s : string) (p : positive) (o : int) : bool :=
  match p with
  | xH => hex_byte_ok s o
  | xO q => hex_ok_pos s q o && hex_ok_pos s q (o + of_Z (Zpos q))%uint63
  | xI q => hex_byte_ok s o && hex_ok_pos s q (o + 1)%uint63
            && hex_ok_pos s q (o + 1 + of_Z (Zpos q))%uint63
  end.

(* [comment removed for export] *)
Definition hex_ok (s : string) (n : Z) : bool :=
  match n with Zpos p => hex_ok_pos s p 0%uint63 | _ => true end.

(* [comment removed for export] *)
Definition mk_fseg (s : Segment) : option fseg :=
  match seg_bytes s with
  | [hex] =>
      let b := Z.of_N (seg_base s) in let n := Z.of_N (seg_size s) in
      if (b mod 4096 =? 0) && (n mod 4096 =? 0) && (b + n <=? 2 ^ 62) && seg_readable s
         && (to_Z (PrimString.length hex) =? 2 * n)
         && (negb (seg_writable s) || hex_ok hex n)
      then Some (SG (of_Z b) (of_Z n) (seg_writable s) hex)
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint segs_disjoint (l : list Segment) : bool :=
  match l with
  | [] => true
  | s :: r =>
      forallb (fun s' => (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? Z.of_N (seg_base s'))
                         || (Z.of_N (seg_base s') + Z.of_N (seg_size s') <=? Z.of_N (seg_base s))) r
      && segs_disjoint r
  end.

(* [comment removed for export] *)
Fixpoint mk_fsegs (l : list Segment) : option fimage :=
  match l with
  | [] => Some []
  | s :: r => match mk_fseg s, mk_fsegs r with
              | Some sg, Some im => Some (sg :: im)
              | _, _ => None
              end
  end.

Definition mk_fimage (segs : list Segment) : option fimage :=
  if segs_disjoint segs then mk_fsegs segs else None.

Fixpoint build_code_acc (segs : list Segment) (pcs : list Z) (acc : itrie finstr) : option (itrie finstr) :=
  match pcs with
  | [] => Some acc
  | pc :: r =>
      if (0 <=? pc) && (pc <? 2 ^ 62) then
        match build_entry segs pc with
        | Some fi => build_code_acc segs r (iset (of_Z pc) fi acc)
        | None => None
        end
      else None
  end.
Definition build_code (segs : list Segment) (pcs : list Z) : option (itrie finstr) :=
  build_code_acc segs pcs iempty.

(* [comment removed for export] *)
Definition fseg_wr_ok (sg : fseg) : Prop :=
  sg_wr sg = true ->
  forall o, 0 <= o < to_Z (sg_size sg) -> hex_byte (sg_hex sg) (of_Z o) <> None.
Definition image_wr_ok (IM : fimage) : Prop := Forall fseg_wr_ok IM.

(* [comment removed for export] *)
Lemma toZ_of_Z_small z : 0 <= z < 2 ^ 63 -> to_Z (of_Z z) = z.
Proof. intros H. rewrite of_Z_spec, i63_wB. apply Z.mod_small. exact H. Qed.

Lemma toZ_add_small (x y : int) : to_Z x + to_Z y < 2 ^ 63 -> to_Z (x + y) = to_Z x + to_Z y.
Proof.
  intros H. rewrite add_spec, i63_wB. apply Z.mod_small.
  pose proof (i63_range x). pose proof (i63_range y). lia.
Qed.

Lemma toZ_sub_small (x y : int) : to_Z y <= to_Z x -> to_Z (x - y) = to_Z x - to_Z y.
Proof.
  intros H. rewrite sub_spec, i63_wB. apply Z.mod_small.
  pose proof (i63_range x). pose proof (i63_range y). lia.
Qed.

Lemma toZ_lsl_small (x : int) (k : Z) (ki : int) :
  to_Z ki = k -> 0 <= k -> to_Z x * 2 ^ k < 2 ^ 63 -> to_Z (x << ki) = to_Z x * 2 ^ k.
Proof.
  intros Hk Hk0 H. rewrite lsl_spec, i63_wB, Hk. apply Z.mod_small.
  pose proof (i63_range x). split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia] | exact H].
Qed.

(* [comment removed for export] *)
Ltac zlia :=
  repeat match goal with
  | |- context [to_Z (sg_base ?s)] => generalize dependent (to_Z (sg_base s)); intros
  | |- context [to_Z (sg_size ?s)] => generalize dependent (to_Z (sg_size s)); intros
  | |- context [Z.of_N (seg_base ?s)] => generalize dependent (Z.of_N (seg_base s)); intros
  | |- context [Z.of_N (seg_size ?s)] => generalize dependent (Z.of_N (seg_size s)); intros
  | H : context [to_Z (sg_base ?s)] |- _ => generalize dependent (to_Z (sg_base s)); intros
  | H : context [to_Z (sg_size ?s)] |- _ => generalize dependent (to_Z (sg_size s)); intros
  | H : context [Z.of_N (seg_base ?s)] |- _ => generalize dependent (Z.of_N (seg_base s)); intros
  | H : context [Z.of_N (seg_size ?s)] |- _ => generalize dependent (Z.of_N (seg_size s)); intros
  end; lia.

Lemma i_ltb_lt (x y : int) : (x <? y)%uint63 = true -> to_Z x < to_Z y.
Proof. intros H. destruct (ltbP x y) as [L|L]; [exact L | discriminate]. Qed.
Lemma i_leb_le (x y : int) : (x <=? y)%uint63 = true -> to_Z x <= to_Z y.
Proof. intros H. destruct (lebP x y) as [L|L]; [exact L | discriminate]. Qed.
Lemma i_ltb_true (x y : int) : to_Z x < to_Z y -> (x <? y)%uint63 = true.
Proof. intros H. destruct (ltbP x y) as [L|L]; [reflexivity | contradiction]. Qed.

(* [comment removed for export] *)
Lemma hex_ok_pos_spec s : forall p o,
  hex_ok_pos s p o = true -> to_Z o + Zpos p <= 2 ^ 62 ->
  forall k, 0 <= k < Zpos p -> hex_byte s (of_Z (to_Z o + k)) <> None.
Proof.
  assert (Hbo : forall o, hex_byte_ok s o = true -> hex_byte s o <> None).
  { intros o H. unfold hex_byte_ok in H. destruct (hex_byte s o); [discriminate | discriminate]. }
  induction p as [q IH | q IH |]; intros o H Hb k Hk; cbn [hex_ok_pos] in H.
  - apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    pose proof (i63_range o) as Ho.
    assert (E1 : to_Z (o + 1)%uint63 = to_Z o + 1).
    { rewrite toZ_add_small; change (to_Z 1) with 1; lia. }
    assert (Eq : to_Z (of_Z (Zpos q)) = Zpos q) by (apply toZ_of_Z_small; lia).
    assert (E2 : to_Z (o + 1 + of_Z (Zpos q))%uint63 = to_Z o + 1 + Zpos q).
    { rewrite toZ_add_small; rewrite E1, Eq; lia. }
    destruct (Z.eq_dec k 0) as [->|Hk0].
    + rewrite Z.add_0_r, of_to_Z. apply Hbo. exact H1.
    + destruct (Z_lt_le_dec k (1 + Zpos q)) as [Hlt|Hge].
      * replace (to_Z o + k) with (to_Z (o + 1)%uint63 + (k - 1)) by lia.
        apply IH; [exact H2 | lia | lia].
      * replace (to_Z o + k) with (to_Z (o + 1 + of_Z (Zpos q))%uint63 + (k - 1 - Zpos q)) by lia.
        apply IH; [exact H3 | lia | lia].
  - apply andb_true_iff in H as [H1 H2].
    pose proof (i63_range o) as Ho.
    assert (Eq : to_Z (of_Z (Zpos q)) = Zpos q) by (apply toZ_of_Z_small; lia).
    assert (E2 : to_Z (o + of_Z (Zpos q))%uint63 = to_Z o + Zpos q).
    { rewrite toZ_add_small; rewrite Eq; lia. }
    destruct (Z_lt_le_dec k (Zpos q)) as [Hlt|Hge].
    + apply IH; [exact H1 | lia | lia].
    + replace (to_Z o + k) with (to_Z (o + of_Z (Zpos q))%uint63 + (k - Zpos q)) by lia.
      apply IH; [exact H2 | lia | lia].
  - assert (k = 0) as -> by lia. rewrite Z.add_0_r, of_to_Z. apply Hbo. exact H.
Qed.

Lemma hex_ok_spec s n :
  hex_ok s n = true -> n <= 2 ^ 62 ->
  forall o, 0 <= o < n -> hex_byte s (of_Z o) <> None.
Proof.
  intros H Hn o Ho. destruct n as [|p|p]; [lia | | lia].
  cbn [hex_ok] in H.
  pose proof (hex_ok_pos_spec s p 0%uint63 H) as HH. change (to_Z 0) with 0 in HH.
  apply (HH ltac:(lia) o Ho).
Qed.

(* [comment removed for export] *)
Lemma mk_fseg_spec s sg :
  mk_fseg s = Some sg ->
  Z.of_N (seg_base s) = to_Z (sg_base sg) /\ Z.of_N (seg_size s) = to_Z (sg_size sg)
  /\ seg_bytes s = [sg_hex sg] /\ seg_readable s = true /\ seg_writable s = sg_wr sg
  /\ to_Z (sg_base sg) mod 4096 = 0 /\ to_Z (sg_size sg) mod 4096 = 0
  /\ to_Z (sg_base sg) + to_Z (sg_size sg) <= 2 ^ 62
  /\ fseg_wr_ok sg.
Proof.
  unfold mk_fseg. destruct (seg_bytes s) as [|hex [|? ?]] eqn:Hb; try discriminate.
  cbv zeta.
  destruct ((Z.of_N (seg_base s) mod 4096 =? 0) && (Z.of_N (seg_size s) mod 4096 =? 0)
            && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 62) && seg_readable s
            && (to_Z (PrimString.length hex) =? 2 * Z.of_N (seg_size s))
            && (negb (seg_writable s) || hex_ok hex (Z.of_N (seg_size s)))) eqn:E; [|discriminate].
  intros H. injection H as <-. cbn [sg_base sg_size sg_wr sg_hex].
  apply andb_true_iff in E as [E E6]. apply andb_true_iff in E as [E E5].
  apply andb_true_iff in E as [E E4]. apply andb_true_iff in E as [E E3].
  apply andb_true_iff in E as [E1 E2].
  apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.leb_le in E3.
  pose proof (N2Z.is_nonneg (seg_base s)) as Hb0. pose proof (N2Z.is_nonneg (seg_size s)) as Hn0.
  rewrite !toZ_of_Z_small by lia.
  repeat split; try assumption; try reflexivity.
  intros Hw o Ho. cbn [sg_wr sg_size sg_hex] in *. rewrite Hw in E6. cbn in E6.
  rewrite toZ_of_Z_small in Ho by lia.
  apply (hex_ok_spec hex (Z.of_N (seg_size s)) E6 ltac:(lia) o Ho).
Qed.

Lemma mk_fsegs_spec : forall l im,
  mk_fsegs l = Some im -> Forall (fun sg => exists s, In s l /\ mk_fseg s = Some sg) im.
Proof.
  induction l as [|s r IH]; intros im H; cbn [mk_fsegs] in H.
  - injection H as <-. constructor.
  - destruct (mk_fseg s) as [sg|] eqn:Hs; [|discriminate].
    destruct (mk_fsegs r) as [im'|] eqn:Hr; [|discriminate].
    injection H as <-. constructor.
    + exists s. split; [left; reflexivity | exact Hs].
    + specialize (IH im' eq_refl). eapply Forall_impl; [|exact IH].
      intros sg' (s' & Hin & Hs'). exists s'. split; [right; exact Hin | exact Hs'].
Qed.

(* [comment removed for export] *)
Lemma find_segment_disjoint : forall l seg a,
  segs_disjoint l = true -> In seg l ->
  Z.of_N (seg_base seg) <= a < Z.of_N (seg_base seg) + Z.of_N (seg_size seg) ->
  find_segment l a 1 = Some seg.
Proof.
  induction l as [|s r IH]; intros seg a Hd Hin Ha; [destruct Hin|].
  cbn [segs_disjoint] in Hd. apply andb_true_iff in Hd as [Hall Hd].
  cbn [find_segment].
  destruct Hin as [->|Hin].
  - replace (Z.leb (Z.of_N (seg_base seg)) a && Z.leb (a + 1) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))
      with true; [reflexivity|].
    symmetry. apply andb_true_iff. split; apply Z.leb_le; lia.
  - destruct (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:E.
    + exfalso. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
      rewrite forallb_forall in Hall. specialize (Hall seg Hin).
      apply orb_true_iff in Hall as [H|H]; apply Z.leb_le in H; lia.
    + apply IH; assumption.
Qed.

(* [comment removed for export] *)
Lemma lor_shift4 x y : 0 <= x -> 0 <= y < 16 -> Z.lor (x * 16) y = x * 16 + y.
Proof.
  intros Hx Hy.
  assert (Hland : Z.land (x * 16) y = 0).
  { change 16 with (2 ^ 4). rewrite <- Z.shiftl_mul_pow2 by lia.
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 4) as [Hlt|Hge].
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - destruct (Z.eq_dec y 0) as [->|Hy0]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 y n); [apply andb_false_r | lia |].
      apply Z.lt_le_trans with 4; [|exact Hge]. apply Z.log2_lt_pow2; [lia | change (2 ^ 4) with 16; lia]. }
  rewrite (Z.add_nocarry_lxor _ _ Hland). symmetry. apply Z.lxor_lor. exact Hland.
Qed.

Lemma nib_spec c h : nib c = Some h -> to_Z h < 16 /\ hex_nybble c = Z.to_N (to_Z h).
Proof.
  unfold nib, hex_nybble. intros H.
  destruct ((48 <=? c)%uint63 && (c <=? 57)%uint63) eqn:E1.
  - injection H as <-. apply andb_true_iff in E1 as [Ea Eb].
    apply i_leb_le in Ea. apply i_leb_le in Eb. change (to_Z 48) with 48 in Ea. change (to_Z 57) with 57 in Eb.
    assert (E : to_Z (c - 48)%uint63 = to_Z c - 48).
    { rewrite toZ_sub_small; change (to_Z 48) with 48; lia. }
    rewrite E. split; [lia | reflexivity].
  - destruct ((97 <=? c)%uint63 && (c <=? 102)%uint63) eqn:E2; [|discriminate].
    injection H as <-. apply andb_true_iff in E2 as [Ea Eb].
    apply i_leb_le in Ea. apply i_leb_le in Eb. change (to_Z 97) with 97 in Ea. change (to_Z 102) with 102 in Eb.
    assert (E : to_Z (c - 87)%uint63 = to_Z c - 87).
    { rewrite toZ_sub_small; change (to_Z 87) with 87; lia. }
    rewrite E. split; [lia | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma hex_byte_spec s o b :
  hex_byte s o = Some b ->
  to_Z b < 256
  /\ (Z.to_N (to_Z o) <? Z.to_N (to_Z (PrimString.length s) / 2))%N = true
  /\ hex_byte_at s (Z.to_N (to_Z o)) = Some (Z_to_bv 8 (to_Z b)).
Proof.
  unfold hex_byte. cbv zeta. intros H.
  destruct ((o <? 2305843009213693952)%uint63 && ((o << 1) + 1 <? PrimString.length s)%uint63) eqn:E; [|discriminate].
  apply andb_true_iff in E as [Eo El]. apply i_ltb_lt in Eo. apply i_ltb_lt in El.
  change (to_Z 2305843009213693952) with (2 ^ 61) in Eo.
  pose proof (i63_range o) as Ho.
  assert (Ei : to_Z (o << 1)%uint63 = 2 * to_Z o).
  { rewrite (toZ_lsl_small o 1 1%uint63); [lia | reflexivity | lia | lia]. }
  assert (Ei1 : to_Z ((o << 1) + 1)%uint63 = 2 * to_Z o + 1).
  { rewrite toZ_add_small; rewrite Ei; change (to_Z 1) with 1; lia. }
  rewrite Ei1 in El.
  destruct (nib (PrimString.get s (o << 1)%uint63)) as [h|] eqn:Hh; [|discriminate].
  destruct (nib (PrimString.get s ((o << 1) + 1)%uint63)) as [l|] eqn:Hl; [|discriminate].
  injection H as <-.
  apply nib_spec in Hh as [Hh16 Hhn]. apply nib_spec in Hl as [Hl16 Hln].
  pose proof (i63_range h) as Hh0. pose proof (i63_range l) as Hl0.
  assert (Eb : to_Z ((h << 4) lor l)%uint63 = to_Z h * 16 + to_Z l).
  { rewrite lor_spec'. rewrite (toZ_lsl_small h 4 4%uint63); [|reflexivity | lia | lia].
    change (2 ^ 4) with 16. apply lor_shift4; lia. }
  assert (Eci : of_Z (Z.of_N (2 * Z.to_N (to_Z o))) = (o << 1)%uint63).
  { apply to_Z_inj. rewrite Ei, toZ_of_Z_small; lia. }
  assert (Eci1 : of_Z (Z.of_N (2 * Z.to_N (to_Z o) + 1)) = ((o << 1) + 1)%uint63).
  { apply to_Z_inj. rewrite Ei1, toZ_of_Z_small; lia. }
  split; [rewrite Eb; lia|]. split.
  - apply N.ltb_lt. pose proof (i63_range (PrimString.length s)) as HL.
    assert (Hq : to_Z o + 1 <= to_Z (PrimString.length s) / 2) by (apply Z.div_le_lower_bound; lia).
    apply Z2N.inj_lt; lia.
  - unfold hex_byte_at. cbv zeta. rewrite Eci, Eci1.
    replace (((o << 1) + 1 <? PrimString.length s)%uint63) with true
      by (symmetry; apply i_ltb_true; rewrite Ei1; exact El).
    cbn [orb]. rewrite Hhn, Hln.
    replace (Z.to_N (to_Z h) <? 16)%N with true by (symmetry; apply N.ltb_lt; lia).
    replace (Z.to_N (to_Z l) <? 16)%N with true by (symmetry; apply N.ltb_lt; lia).
    cbn [andb]. f_equal. f_equal. rewrite Eb. lia.
Qed.

Lemma seg_byte_hex s o b :
  hex_byte s o = Some b ->
  segment_byte_at [s] (Z.to_N (to_Z o)) = Some (Z_to_bv 8 (to_Z b)) /\ to_Z b < 256.
Proof.
  intros H. apply hex_byte_spec in H as (Hb & Hlt & Hat).
  split; [|exact Hb]. cbn [segment_byte_at]. rewrite Hlt. exact Hat.
Qed.

Lemma find_seg_spec : forall IM a sg,
  find_seg IM a = Some sg ->
  In sg IM /\ (sg_base sg <=? a)%uint63 = true /\ (a <? sg_base sg + sg_size sg)%uint63 = true.
Proof.
  induction IM as [|sg0 r IH]; intros a sg H; cbn [find_seg] in H; [discriminate|].
  destruct ((sg_base sg0 <=? a)%uint63 && (a <? sg_base sg0 + sg_size sg0)%uint63) eqn:E.
  - injection H as <-. apply andb_true_iff in E as [E1 E2]. split; [left; reflexivity | split; assumption].
  - destruct (IH a sg H) as (Hin & H1 & H2). split; [right; exact Hin | split; assumption].
Qed.

Section ImageSound.
Variable segs : list Segment.

Theorem mk_fimage_ok : forall IM, mk_fimage segs = Some IM -> image_ok segs IM.
Proof.
  intros IM H. unfold mk_fimage in H.
  destruct (segs_disjoint segs) eqn:Hd; [|discriminate].
  apply mk_fsegs_spec in H. unfold image_ok. eapply Forall_impl; [|exact H].
  intros sg (s & Hin & Hs). apply mk_fseg_spec in Hs.
  destruct Hs as (Eb & En & Ebytes & Er & Ew & Mb & Mn & Hle & _).
  exists s. repeat split; try assumption.
  intros a Ha. apply find_segment_disjoint; [exact Hd | exact Hin |].
  rewrite Eb, En. exact Ha.
Qed.

Theorem mk_fimage_wr_ok : forall IM, mk_fimage segs = Some IM -> image_wr_ok IM.
Proof.
  intros IM H. unfold mk_fimage in H.
  destruct (segs_disjoint segs) eqn:Hd; [|discriminate].
  apply mk_fsegs_spec in H. unfold image_wr_ok. eapply Forall_impl; [|exact H].
  intros sg (s & Hin & Hs). apply mk_fseg_spec in Hs. apply Hs.
Qed.

Lemma build_code_acc_ok : forall pcs acc C,
  code_ok segs acc -> build_code_acc segs pcs acc = Some C -> code_ok segs C.
Proof.
  induction pcs as [|pc r IH]; intros acc C Hacc H; cbn [build_code_acc] in H.
  - injection H as <-. exact Hacc.
  - destruct ((0 <=? pc) && (pc <? 2 ^ 62)) eqn:E; [|discriminate].
    apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    destruct (build_entry segs pc) as [fi|] eqn:Hfi; [|discriminate].
    apply (IH (iset (of_Z pc) fi acc) C); [|exact H].
    intros k fi' Hk. rewrite iget_iset in Hk.
    destruct (k =? of_Z pc)%uint63 eqn:Ek.
    + apply Uint63.eqb_spec in Ek. subst k. injection Hk as <-.
      rewrite toZ_of_Z_small by lia. exact Hfi.
    + apply Hacc. exact Hk.
Qed.

Theorem build_code_ok : forall pcs C, build_code segs pcs = Some C -> code_ok segs C.
Proof.
  intros pcs C H. apply (build_code_acc_ok pcs iempty C); [|exact H].
  intros k fi Hk. rewrite iget_iempty in Hk. discriminate.
Qed.

(* [comment removed for export] *)
Lemma memory_read_hex sg A oj b :
  fseg_ok segs sg ->
  to_Z (sg_base sg) <= A < to_Z (sg_base sg) + to_Z (sg_size sg) ->
  to_Z oj = A - to_Z (sg_base sg) ->
  hex_byte (sg_hex sg) oj = Some b ->
  memory_read segs (Z_to_bv 64 A) 1 = Some [Z_to_bv 8 (to_Z b)].
Proof.
  intros (seg & Hin & Eb & En & Ebytes & Er & Ew & Mb & Mn & Hle & Hfind) HA Hoj Hb.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    pose proof (i63_range (sg_base sg)) as H0. clear - HA Hle H0. zlia. }
  unfold memory_read. rewrite EA. change (Z.of_N 1) with 1. rewrite (Hfind A HA), Er, Ebytes.
  replace (Z.to_N (A - Z.of_N (seg_base seg))) with (Z.to_N (to_Z oj)) by (rewrite Hoj, Eb; reflexivity).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (seg_byte_hex _ _ _ Hb) as [Hs _]. rewrite Hs. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem image_cell_sound : forall IM a8 w,
  image_ok segs IM ->
  to_Z a8 mod 8 = 0 ->
  image_cell IM a8 = Some (FV 0%uint63 w) ->
  forall j, (j < 8)%nat ->
    memory_read segs (Z_to_bv 64 (to_Z a8 + Z.of_nat j)) 1 = option_map (fun b => [b]) (nth_error (Z_to_le_bytes 8 (wZ w)) j).
Proof.
  intros IM a8 w HIM Hal Hc j Hj. unfold image_cell in Hc.
  destruct (find_seg IM a8) as [sg|] eqn:Hf; [|discriminate].
  destruct (hex_cell (sg_hex sg) (a8 - sg_base sg)%uint63) as [w'|] eqn:Hh; [|discriminate].
  injection Hc as <-.
  apply find_seg_spec in Hf as (Hin & H1 & H2).
  pose proof (proj1 (Forall_forall _ _) HIM sg Hin) as Hsg.
  assert (Hnum : to_Z (sg_base sg) <= to_Z a8 /\ to_Z a8 + 8 <= to_Z (sg_base sg) + to_Z (sg_size sg)
                 /\ to_Z (sg_base sg) + to_Z (sg_size sg) <= 2 ^ 62).
  { destruct Hsg as (seg & _ & _ & _ & _ & _ & _ & Mb & Mn & Hle & _).
    apply i_leb_le in H1. apply i_ltb_lt in H2.
    pose proof (i63_range (sg_base sg)) as Hb0. pose proof (i63_range (sg_size sg)) as Hn0.
    rewrite toZ_add_small in H2 by (clear - Hle Hb0 Hn0; zlia).
    pose proof (Z.div_mod (to_Z a8) 8 ltac:(discriminate)) as Da. rewrite Hal in Da.
    pose proof (Z.div_mod (to_Z (sg_base sg)) 4096 ltac:(discriminate)) as Db. rewrite Mb in Db.
    pose proof (Z.div_mod (to_Z (sg_size sg)) 4096 ltac:(discriminate)) as Dn. rewrite Mn in Dn.
    clear - H1 H2 Hle Da Db Dn Hb0 Hn0.
    generalize dependent (to_Z a8 / 8). generalize dependent (to_Z (sg_base sg) / 4096).
    generalize dependent (to_Z (sg_size sg) / 4096). intros qn Dn qb Db qa Da. zlia. }
  destruct Hnum as (HB & HT & Hle).
  pose proof (i63_range (sg_base sg)) as Hb0.
  assert (Eo : to_Z (a8 - sg_base sg)%uint63 = to_Z a8 - to_Z (sg_base sg)) by (apply toZ_sub_small; exact HB).
  assert (Eok : forall k : int, to_Z k < 8 ->
                to_Z (a8 - sg_base sg + k)%uint63 = to_Z a8 + to_Z k - to_Z (sg_base sg)).
  { intros k Hk. pose proof (i63_range k). rewrite toZ_add_small; rewrite Eo; clear - HB HT Hle Hb0 Hk H; zlia. }
  unfold hex_cell in Hh.
  destruct (hex_byte (sg_hex sg) (a8 - sg_base sg)%uint63) as [b0|] eqn:B0; [|discriminate].
  destruct (hex_byte (sg_hex sg) (a8 - sg_base sg + 1)%uint63) as [b1|] eqn:B1; [|discriminate].
  destruct (hex_byte (sg_hex sg) (a8 - sg_base sg + 2)%uint63) as [b2|] eqn:B2; [|discriminate].
  destruct (hex_byte (sg_hex sg) (a8 - sg_base sg + 3)%uint63) as [b3|] eqn:B3; [|discriminate].
  destruct (hex_byte (sg_hex sg) (a8 - sg_base sg + 4)%uint63) as [b4|] eqn:B4; [|discriminate].
  destruct (hex_byte (sg_hex sg) (a8 - sg_base sg + 5)%uint63) as [b5|] eqn:B5; [|discriminate].
  destruct (hex_byte (sg_hex sg) (a8 - sg_base sg + 6)%uint63) as [b6|] eqn:B6; [|discriminate].
  destruct (hex_byte (sg_hex sg) (a8 - sg_base sg + 7)%uint63) as [b7|] eqn:B7; [|discriminate].
  injection Hh as <-.
  change (Z_to_le_bytes 8 (wZ (w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7))) with (w_bytes (w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7)).
  rewrite w_bytes_w_of_bytes8 by
    (match goal with |- to_Z ?b < 256 =>
       match goal with Hb : hex_byte _ _ = Some b |- _ => exact (proj1 (hex_byte_spec _ _ _ Hb)) end end).
  destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; [| | | | | | | | exfalso; clear - Hj; lia];
    cbn [nth_error option_map];
    match goal with |- memory_read _ (Z_to_bv 64 (_ + Z.of_nat ?n)) _ = _ =>
      let z := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with z end.
  - apply (memory_read_hex sg _ (a8 - sg_base sg)%uint63 b0 Hsg); [clear - HB HT; zlia | rewrite Eo; clear; zlia | exact B0].
  - apply (memory_read_hex sg _ (a8 - sg_base sg + 1)%uint63 b1 Hsg); [clear - HB HT; zlia | rewrite Eok by (change (to_Z 1) with 1; lia); change (to_Z 1) with 1; clear; zlia | exact B1].
  - apply (memory_read_hex sg _ (a8 - sg_base sg + 2)%uint63 b2 Hsg); [clear - HB HT; zlia | rewrite Eok by (change (to_Z 2) with 2; lia); change (to_Z 2) with 2; clear; zlia | exact B2].
  - apply (memory_read_hex sg _ (a8 - sg_base sg + 3)%uint63 b3 Hsg); [clear - HB HT; zlia | rewrite Eok by (change (to_Z 3) with 3; lia); change (to_Z 3) with 3; clear; zlia | exact B3].
  - apply (memory_read_hex sg _ (a8 - sg_base sg + 4)%uint63 b4 Hsg); [clear - HB HT; zlia | rewrite Eok by (change (to_Z 4) with 4; lia); change (to_Z 4) with 4; clear; zlia | exact B4].
  - apply (memory_read_hex sg _ (a8 - sg_base sg + 5)%uint63 b5 Hsg); [clear - HB HT; zlia | rewrite Eok by (change (to_Z 5) with 5; lia); change (to_Z 5) with 5; clear; zlia | exact B5].
  - apply (memory_read_hex sg _ (a8 - sg_base sg + 6)%uint63 b6 Hsg); [clear - HB HT; zlia | rewrite Eok by (change (to_Z 6) with 6; lia); change (to_Z 6) with 6; clear; zlia | exact B6].
  - apply (memory_read_hex sg _ (a8 - sg_base sg + 7)%uint63 b7 Hsg); [clear - HB HT; zlia | rewrite Eok by (change (to_Z 7) with 7; lia); change (to_Z 7) with 7; clear; zlia | exact B7].
Qed.

Lemma bv_add_0_Z_to_bv (x : bv 64) : bv_add (Z_to_bv 64 0) x = x.
Proof.
  apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned, bv_wrap_0, Z.add_0_l.
  apply bv_wrap_bv_unsigned.
Qed.

Lemma image_cell_tag IM a v : image_cell IM a = Some v -> exists w, v = FV 0%uint63 w.
Proof.
  unfold image_cell. destruct (find_seg IM a) as [sg|]; [|discriminate].
  destruct (hex_cell (sg_hex sg) (a - sg_base sg)%uint63) as [w|]; [|discriminate].
  intros H. injection H as <-. exists w. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem page_ok_image_init : forall IM rho m pn sg,
  image_ok segs IM ->
  image_wr_ok IM ->
  rho 0%uint63 = Z_to_bv 64 0 ->
  to_Z pn < 2 ^ 50 ->
  find_seg IM (pn << 12)%uint63 = Some sg ->
  (forall a, to_Z (sg_base sg) <= a < to_Z (sg_base sg) + to_Z (sg_size sg) -> m (Z_to_bv 64 a) = None) ->
  page_ok segs IM rho m 0%uint63 pn 512 (PG (sg_wr sg) PKImage iempty).
Proof.
  intros IM rho m pn sg HIM HWR Hrho Hpn Hf Hm.
  destruct (find_seg_spec _ _ _ Hf) as (Hin & H1 & H2).
  pose proof (proj1 (Forall_forall _ _) HIM sg Hin) as Hsg.
  pose proof (proj1 (Forall_forall _ _) HWR sg Hin) as Hwr.
  pose proof (i63_range pn) as Hpn0.
  assert (Epn : to_Z (pn << 12)%uint63 = to_Z pn * 4096).
  { rewrite (toZ_lsl_small pn 12 12%uint63); [reflexivity | reflexivity | lia | change (2 ^ 12) with 4096; lia]. }
  assert (Hnum : to_Z (sg_base sg) <= to_Z pn * 4096
                 /\ to_Z pn * 4096 + 4096 <= to_Z (sg_base sg) + to_Z (sg_size sg)
                 /\ to_Z (sg_base sg) + to_Z (sg_size sg) <= 2 ^ 62).
  { destruct Hsg as (seg & _ & _ & _ & _ & _ & _ & Mb & Mn & Hle & _).
    apply i_leb_le in H1. apply i_ltb_lt in H2. rewrite Epn in H1, H2.
    pose proof (i63_range (sg_base sg)) as Hb0. pose proof (i63_range (sg_size sg)) as Hn0.
    rewrite toZ_add_small in H2 by (clear - Hle Hb0 Hn0; zlia).
    pose proof (Z.div_mod (to_Z (sg_base sg)) 4096 ltac:(discriminate)) as Db. rewrite Mb in Db.
    pose proof (Z.div_mod (to_Z (sg_size sg)) 4096 ltac:(discriminate)) as Dn. rewrite Mn in Dn.
    clear - H1 H2 Hle Db Dn Hb0 Hn0.
    generalize dependent (to_Z (sg_base sg) / 4096).
    generalize dependent (to_Z (sg_size sg) / 4096). intros qn Dn qb Db. zlia. }
  destruct Hnum as (HB & HT & Hle).
  pose proof (i63_range (sg_base sg)) as Hb0.
  assert (Hadr : forall z, adr rho 0%uint63 z = Z_to_bv 64 z).
  { intros z. unfold adr. rewrite Hrho. apply bv_add_0_Z_to_bv. }
  split; [|split].
  - (* [comment removed for export] *)
    cbn [pg_wr]. intros Hw j Hj. rewrite Hadr. unfold wview.
    assert (Hr : to_Z (sg_base sg) <= to_Z pn * 4096 + j < to_Z (sg_base sg) + to_Z (sg_size sg))
      by (clear - HB HT Hj; zlia).
    rewrite (Hm _ Hr).
    destruct Hsg as (seg & _ & Eb & En & Ebytes & Er & Ew & _ & _ & _ & Hfind).
    assert (EA : bv_unsigned (Z_to_bv 64 (to_Z pn * 4096 + j)) = to_Z pn * 4096 + j).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      clear - Hr Hle Hb0. zlia. }
    rewrite EA, (Hfind _ Hr), Ew, Hw, Ebytes.
    assert (Ho : 0 <= to_Z pn * 4096 + j - to_Z (sg_base sg) < to_Z (sg_size sg)) by (clear - Hr; zlia).
    specialize (Hwr Hw _ Ho).
    destruct (hex_byte (sg_hex sg) (of_Z (to_Z pn * 4096 + j - to_Z (sg_base sg)))) as [b|] eqn:Hb; [|congruence].
    destruct (seg_byte_hex _ _ _ Hb) as [Hs _].
    rewrite toZ_of_Z_small in Hs by (clear - Ho Hle Hb0 Hr; zlia).
    rewrite Eb, Hs. discriminate.
  - (* [comment removed for export] *)
    intros ci v Hci Hcell j Hj. unfold cell_at in Hcell. cbn [pg_cells pg_kind] in Hcell.
    rewrite iget_iempty in Hcell.
    destruct (image_cell_tag _ _ _ Hcell) as [w ->].
    assert (Eci : to_Z (ci << 3)%uint63 = to_Z ci * 8).
    { rewrite (toZ_lsl_small ci 3 3%uint63); [reflexivity | reflexivity | lia | change (2 ^ 3) with 8; lia]. }
    assert (Ea8 : to_Z ((pn << 12) + (ci << 3))%uint63 = to_Z pn * 4096 + to_Z ci * 8).
    { rewrite toZ_add_small; rewrite Epn, Eci; [reflexivity | lia]. }
    assert (Hal : to_Z ((pn << 12) + (ci << 3))%uint63 mod 8 = 0).
    { rewrite Ea8. replace (to_Z pn * 4096 + to_Z ci * 8) with ((to_Z pn * 512 + to_Z ci) * 8) by ring.
      apply Z.mod_mul. discriminate. }
    pose proof (image_cell_sound IM _ w HIM Hal Hcell j Hj) as Hrd. rewrite Ea8 in Hrd.
    rewrite Hadr. unfold rview.
    assert (Hr : to_Z (sg_base sg) <= to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j < to_Z (sg_base sg) + to_Z (sg_size sg))
      by (clear - HB HT Hj Hci; zlia).
    rewrite (Hm _ Hr), Hrd.
    unfold wbytes8.
    replace (dv rho (FV 0%uint63 w)) with (wbv w)
      by (unfold dv, dvk; cbn; rewrite Hrho, bv_add_0_Z_to_bv; reflexivity).
    rewrite wbv_unsigned.
    destruct (nth_error (Z_to_le_bytes 8 (wZ w)) j); reflexivity.
  - (* [comment removed for export] *)
    intros ci sl Hci Hcb. cbn [pg_cells] in Hcb. rewrite iget_iempty in Hcb. discriminate.
Qed.

End ImageSound.

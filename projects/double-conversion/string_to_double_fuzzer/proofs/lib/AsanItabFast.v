(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require PrimInt63 Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC.
Import PrimInt63.
Open Scope Z_scope.

Section ItabFast.
Variable SEGS : list Segment.

#[local] Notation φ := Uint63.to_Z.
Lemma wB_val : Uint63.wB = 2 ^ 63. Proof. reflexivity. Qed.

Lemma i63_vals : φ i63_1 = 1 /\ φ i63_2 = 2 /\ φ i63_4 = 4 /\ φ i63_6 = 6 /\ φ i63_8 = 8 /\ φ i63_16 = 16 /\ φ i63_48 = 48
                 /\ φ i63_57 = 57 /\ φ i63_87 = 87 /\ φ i63_97 = 97 /\ φ i63_102 = 102 /\ φ i63_256 = 256.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma hexv63_spec : forall c, φ (hexv63 c) = Z.of_N (hex_nybble c).
Proof.
  intros c. pose proof i63_vals as (V1 & V2 & V4 & V6 & V8 & V16 & V48 & V57 & V87 & V97 & V102 & V256).
  pose proof (Uint63.to_Z_bounded c) as Bc. rewrite wB_val in Bc.
  unfold hexv63, hex_nybble. cbv delta [i63_48 i63_57 i63_97 i63_102 i63_87 i63_16].
  cbv delta [i63_48 i63_57 i63_97 i63_102 i63_87 i63_16] in V16, V48, V57, V87, V97, V102.
  destruct (Uint63.leb 48%uint63 c) eqn:E1; destruct (Uint63.leb c 57%uint63) eqn:E2; cbn [andb].
  1: { apply Uint63.leb_spec in E1. apply Uint63.leb_spec in E2. rewrite V48 in E1. rewrite V57 in E2.
       rewrite Uint63.sub_spec, V48, wB_val, Z.mod_small by lia. rewrite Z2N.id by lia. reflexivity. }
  all: destruct (Uint63.leb 97%uint63 c) eqn:E3; destruct (Uint63.leb c 102%uint63) eqn:E4; cbn [andb]; try (rewrite V16; reflexivity).
  all: apply Uint63.leb_spec in E3; apply Uint63.leb_spec in E4; rewrite V97 in E3; rewrite V102 in E4;
       rewrite Uint63.sub_spec, V87, wB_val, Z.mod_small by lia; rewrite Z2N.id by lia; reflexivity.
Qed.


(* [comment removed for export] *)
Lemma ltb63 : forall x y, Uint63.ltb x y = Z.ltb (φ x) (φ y).
Proof.
  intros x y. destruct (Uint63.ltb x y) eqn:E.
  - apply Uint63.ltb_spec in E. symmetry. apply Z.ltb_lt. exact E.
  - symmetry. apply Z.ltb_ge. destruct (Z.ltb (φ x) (φ y)) eqn:E2; [|lia]. apply Z.ltb_lt in E2.
    apply (proj2 (Uint63.ltb_spec x y)) in E2. congruence.
Qed.
Lemma eqb63 : forall x y, Uint63.eqb x y = Z.eqb (φ x) (φ y).
Proof.
  intros x y. destruct (Uint63.eqb x y) eqn:E.
  - apply Uint63.eqb_spec in E. subst. symmetry. apply Z.eqb_refl.
  - symmetry. apply Z.eqb_neq. intros H. apply Uint63.to_Z_inj in H. subst. rewrite (proj2 (Uint63.eqb_spec y y) eq_refl) in E. discriminate.
Qed.

(* [comment removed for export] *)
Lemma hexb63_spec : forall s n i,
  φ i = 2 * Z.of_N n -> 2 * Z.of_N n + 1 < φ (PrimString.length s) ->
  hex_byte_at s n = (if Uint63.ltb (hexb63 s i) i63_256 then Some (Z_to_bv 8 (φ (hexb63 s i))) else None)
  /\ φ (hexb63 s i) <= 256.
Proof.
  intros s n i Hi Hlen. pose proof i63_vals as (V1 & V2 & V4 & V6 & V8 & V16 & V48 & V57 & V87 & V97 & V102 & V256).
  pose proof (Uint63.to_Z_bounded (PrimString.length s)) as BL. rewrite wB_val in BL.
  unfold hex_byte_at, hexb63.
  assert (Eci : Uint63.of_Z (Z.of_N (2 * n)) = i).
  { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, wB_val, Z.mod_small; lia. }
  assert (Eci1 : Uint63.of_Z (Z.of_N (2 * n + 1)) = Uint63.add i i63_1).
  { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, Uint63.add_spec, V1, wB_val, !Z.mod_small; lia. }
  rewrite Eci, Eci1.
  assert (Hci1 : φ (Uint63.add i i63_1) = 2 * Z.of_N n + 1).
  { rewrite Uint63.add_spec, V1, wB_val, Z.mod_small; lia. }
  rewrite (ltb63 (Uint63.add i i63_1)), Hci1. replace (2 * Z.of_N n + 1 <? φ (PrimString.length s)) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [orb].
  set (hc := PrimString.get s i). set (lc := PrimString.get s (Uint63.add i i63_1)).
  pose proof (hexv63_spec hc) as Hh. pose proof (hexv63_spec lc) as Hl.
  set (h := hexv63 hc) in *. set (l := hexv63 lc) in *.
  rewrite (ltb63 h i63_16), (ltb63 l i63_16), V16, Hh, Hl.
  destruct (N.ltb (hex_nybble hc) 16) eqn:Eh; destruct (N.ltb (hex_nybble lc) 16) eqn:El;
    rewrite ?N.ltb_lt, ?N.ltb_ge in Eh; rewrite ?N.ltb_lt, ?N.ltb_ge in El.
  - replace (Z.of_N (hex_nybble hc) <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (Z.of_N (hex_nybble lc) <? 16) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    assert (HV : φ (Uint63.add (Uint63.lsl h i63_4) l) = Z.of_N (hex_nybble hc * 16 + hex_nybble lc)).
    { rewrite Uint63.add_spec, Uint63.lsl_spec, V4, Hh, Hl, wB_val. change (2 ^ 4) with 16. rewrite !Z.mod_small; lia. }
    rewrite (ltb63 _ i63_256), V256, HV. replace (Z.of_N (hex_nybble hc * 16 + hex_nybble lc) <? 256) with true by (symmetry; apply Z.ltb_lt; lia).
    split; [reflexivity | lia].
  - replace (Z.of_N (hex_nybble lc) <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (Z.of_N (hex_nybble hc) <? 16); cbn [andb]; rewrite (ltb63 _ i63_256), V256, Z.ltb_irrefl; split; first [reflexivity | lia].
  - replace (Z.of_N (hex_nybble hc) <? 16) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
    rewrite (ltb63 _ i63_256), V256, Z.ltb_irrefl. split; [reflexivity | lia].
  - replace (Z.of_N (hex_nybble hc) <? 16) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
    rewrite (ltb63 _ i63_256), V256, Z.ltb_irrefl. split; [reflexivity | lia].
Qed.

(* [comment removed for export] *)
Definition rd4 (c : PrimString.string) (n : N) : option (bv 32) :=
  match hex_byte_at c n, hex_byte_at c (n + 1)%N, hex_byte_at c (n + 2)%N, hex_byte_at c (n + 3)%N with
  | Some b0, Some b1, Some b2, Some b3 => Some (le4 b3 b2 b1 b0)
  | _, _, _, _ => None
  end.

Lemma lor_bound : forall a b k, 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros a b k Ha Hb. split; [apply Z.lor_nonneg; lia|].
  assert (Hk : 0 <= k) by (destruct (Z.neg_nonneg_cases k) as [Hk|Hk]; [rewrite Z.pow_neg_r in Ha by lia; lia | exact Hk]).
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
  assert (Hpos : 0 < Z.lor a b).
  { pose proof (Z.lor_nonneg a b). destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [apply Z.lor_eq_0_l in E; lia | lia]. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) k Hpos)). rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; [apply (proj1 (Z.log2_lt_pow2 a k ltac:(lia))) | apply (proj1 (Z.log2_lt_pow2 b k ltac:(lia)))]; lia.
Qed.

Lemma le4_val : forall (b3 b2 b1 b0 : byte) z,
  z = Z.lor (bv_unsigned b0) ((Z.lor (bv_unsigned b1) ((Z.lor (bv_unsigned b2) (bv_unsigned b3 * 2 ^ 8)) * 2 ^ 8)) * 2 ^ 8) ->
  Z_to_bv 32 z = le4 b3 b2 b1 b0.
Proof.
  intros b3 b2 b1 b0 z Hz. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (le4_spec b3 b2 b1 b0) as X. cbn [bytes_le_to_Z] in X.
  rewrite Z.shiftl_0_l, Z.lor_0_r, !Z.shiftl_mul_pow2 in X by lia.
  rewrite X, <- Hz. apply bv_wrap_small. rewrite Hz, <- X. apply bv_unsigned_in_range.
Qed.

Lemma u_Z2bv8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

Lemma hexw63_spec : forall c n i,
  φ i = 2 * Z.of_N n -> 2 * Z.of_N n + 7 < φ (PrimString.length c) ->
  match hexw63 c i with Some z => Some (Z_to_bv 32 z) | None => None end = rd4 c n.
Proof.
  intros c n i Hi Hlen. pose proof i63_vals as (V1 & V2 & V4 & V6 & V8 & V16 & V48 & V57 & V87 & V97 & V102 & V256).
  pose proof (Uint63.to_Z_bounded (PrimString.length c)) as BL. rewrite wB_val in BL.
  unfold rd4, hexw63.
  (* [comment removed for export] *)
  remember (Uint63.add i i63_2) as i2 eqn:Ei2. remember (Uint63.add i i63_4) as i4 eqn:Ei4. remember (Uint63.add i i63_6) as i6 eqn:Ei6.
  assert (A2 : φ i2 = 2 * Z.of_N (n + 1)).
  { subst i2. clear Ei4 Ei6. rewrite Uint63.add_spec, V2, wB_val. rewrite Z.mod_small; lia. }
  assert (A4 : φ i4 = 2 * Z.of_N (n + 2)).
  { subst i4. clear Ei2 Ei6 A2. rewrite Uint63.add_spec, V4, wB_val. rewrite Z.mod_small; lia. }
  assert (A6 : φ i6 = 2 * Z.of_N (n + 3)).
  { subst i6. clear Ei2 Ei4 A2 A4. rewrite Uint63.add_spec, V6, wB_val. rewrite Z.mod_small; lia. }
  clear Ei2 Ei4 Ei6.
  destruct (hexb63_spec c n i Hi ltac:(lia)) as [E0 B0].
  destruct (hexb63_spec c (n + 1)%N i2 A2 ltac:(lia)) as [E1 B1].
  destruct (hexb63_spec c (n + 2)%N i4 A4 ltac:(lia)) as [E2 B2].
  destruct (hexb63_spec c (n + 3)%N i6 A6 ltac:(lia)) as [E3 B3].
  rewrite E0, E1, E2, E3.
  set (b0 := hexb63 c i) in *. set (b1 := hexb63 c i2) in *. set (b2 := hexb63 c i4) in *. set (b3 := hexb63 c i6) in *.
  pose proof (Uint63.to_Z_bounded b0) as R0. pose proof (Uint63.to_Z_bounded b1) as R1.
  pose proof (Uint63.to_Z_bounded b2) as R2. pose proof (Uint63.to_Z_bounded b3) as R3.
  clear Hi A2 A4 A6 Hlen BL.
  rewrite !ltb63, V256.
  destruct (φ b0 <? 256) eqn:L0; [apply Z.ltb_lt in L0|apply Z.ltb_ge in L0]; cbn [andb]; [|reflexivity].
  destruct (φ b1 <? 256) eqn:L1; [apply Z.ltb_lt in L1|apply Z.ltb_ge in L1]; cbn [andb]; [|reflexivity].
  destruct (φ b2 <? 256) eqn:L2; [apply Z.ltb_lt in L2|apply Z.ltb_ge in L2]; cbn [andb]; [|reflexivity].
  destruct (φ b3 <? 256) eqn:L3; [apply Z.ltb_lt in L3|apply Z.ltb_ge in L3]; cbn [andb]; [|reflexivity].
  f_equal. apply le4_val. rewrite !u_Z2bv8 by lia.
  (* [comment removed for export] *)
  remember (Uint63.lsl b3 i63_8) as t3 eqn:Et3.
  assert (T3 : φ t3 = φ b3 * 2 ^ 8) by (subst t3; rewrite Uint63.lsl_spec, V8, wB_val; apply Z.mod_small; lia). clear Et3.
  remember (Uint63.lor b2 t3) as u2 eqn:Eu2.
  assert (U2 : φ u2 = Z.lor (φ b2) (φ b3 * 2 ^ 8)) by (subst u2; rewrite Uint63.lor_spec', T3; reflexivity). clear Eu2.
  pose proof (lor_bound (φ b2) (φ b3 * 2 ^ 8) 16 ltac:(lia) ltac:(change (2 ^ 16) with (2 ^ 8 * 2 ^ 8); lia)) as X2. rewrite <- U2 in X2.
  remember (Uint63.lsl u2 i63_8) as t2 eqn:Et2.
  assert (T2 : φ t2 = φ u2 * 2 ^ 8) by (subst t2; rewrite Uint63.lsl_spec, V8, wB_val; apply Z.mod_small; change (2 ^ 63) with (2 ^ 16 * 2 ^ 47); lia). clear Et2.
  remember (Uint63.lor b1 t2) as u1 eqn:Eu1.
  assert (U1 : φ u1 = Z.lor (φ b1) (φ u2 * 2 ^ 8)) by (subst u1; rewrite Uint63.lor_spec', T2; reflexivity). clear Eu1.
  pose proof (lor_bound (φ b1) (φ u2 * 2 ^ 8) 24 ltac:(lia) ltac:(change (2 ^ 24) with (2 ^ 16 * 2 ^ 8); lia)) as X1. rewrite <- U1 in X1.
  remember (Uint63.lsl u1 i63_8) as t1 eqn:Et1.
  assert (T1 : φ t1 = φ u1 * 2 ^ 8) by (subst t1; rewrite Uint63.lsl_spec, V8, wB_val; apply Z.mod_small; change (2 ^ 63) with (2 ^ 24 * 2 ^ 39); lia). clear Et1.
  rewrite Uint63.lor_spec', T1, U1, U2. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma page_segment_find : forall ss lo len sg pc,
  page_segment ss lo len = Some sg -> lo <= pc -> pc + 4 <= lo + len ->
  find_segment ss pc 4 = Some sg.
Proof.
  induction ss as [|s0 rest IH]; intros lo len sg pc H Hlo Hhi; cbn [page_segment] in H; [discriminate|].
  cbn [find_segment].
  destruct (Z.leb (Z.of_N (seg_base s0)) lo && Z.leb (lo + len) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool eqn:E.
  - injection H as ->. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    replace (Z.of_N (seg_base sg) <=? pc) with true by (symmetry; apply Z.leb_le; lia).
    replace (pc + 4 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - destruct (Z.leb (lo + len) (Z.of_N (seg_base s0)) || Z.leb (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) lo)%bool eqn:D; [|discriminate].
    assert (NC : ((Z.of_N (seg_base s0) <=? pc) && (pc + 4 <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool = false).
    { apply orb_prop in D as [D|D]; apply Z.leb_le in D.
      - apply andb_false_intro1. apply Z.leb_gt. lia.
      - apply andb_false_intro2. apply Z.leb_gt. lia. }
    rewrite NC. exact (IH lo len sg pc H Hlo Hhi).
Qed.

(* [comment removed for export] *)
Lemma segment_read4 : forall c off,
  (Z.of_N off + 4 <= Uint63.to_Z (PrimString.length c) / 2) ->
  segment_read_bytes [c] off 4 =
  match hex_byte_at c off, hex_byte_at c (off + 1)%N, hex_byte_at c (off + 2)%N, hex_byte_at c (off + 3)%N with
  | Some b0, Some b1, Some b2, Some b3 => Some [b0; b1; b2; b3]
  | _, _, _, _ => None
  end.
Proof.
  intros c off Hoff.
  assert (SB : forall m, (Z.of_N m < Uint63.to_Z (PrimString.length c) / 2) -> segment_byte_at [c] m = hex_byte_at c m).
  { intros m Hm. cbn [segment_byte_at].
    replace (m <? Z.to_N (Uint63.to_Z (PrimString.length c) / 2))%N with true; [reflexivity|].
    symmetry. apply N.ltb_lt. lia. }
  cbn [segment_read_bytes]. rewrite !SB by lia.
  replace (off + 1 + 1)%N with (off + 2)%N by lia. replace (off + 2 + 1)%N with (off + 3)%N by lia.
  destruct (hex_byte_at c off); [|reflexivity]. destruct (hex_byte_at c (off + 1)%N); [|reflexivity].
  destruct (hex_byte_at c (off + 2)%N); [|reflexivity]. destruct (hex_byte_at c (off + 3)%N); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma page_fast_entry : forall lo n c i0,
  page_fast_ok SEGS lo n = Some (c, i0) ->
  (φ i0 + 8 * Z.of_nat n < 2 ^ 63)
  /\ forall k i', (k < n)%nat -> φ i' = φ i0 + 8 * Z.of_nat k ->
     fast_entry c i' = itab_entry SEGS (lo + 4 * Z.of_nat k).
Proof.
  intros lo n c i0 H. unfold page_fast_ok in H.
  match type of H with (if negb ?g then None else _) = _ => destruct g eqn:G; [cbn [negb] in H|discriminate] end.
  apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
  apply Z.eqb_eq in G1. apply Z.leb_le in G2. apply Z.ltb_lt in G3. apply Z.ltb_lt in G4. change two64 with (2 ^ 64) in G3.
  destruct (page_segment SEGS lo (4 * Z.of_nat n)) as [sg|] eqn:PS; [|discriminate].
  destruct (seg_executable sg && negb (seg_writable sg))%bool eqn:PERM; [cbn [negb] in H|discriminate].
  destruct (seg_bytes sg) as [|c0 [|c1 cs]] eqn:SB; try discriminate.
  match type of H with (if ?g then _ else _) = _ => destruct g eqn:R; [|discriminate] end.
  apply andb_prop in R as [R R3]. apply andb_prop in R as [R1 R2]. apply Z.leb_le in R1. apply Z.leb_le in R2. apply Z.ltb_lt in R3.
  assert (Ec : c0 = c) by congruence. assert (Ei0 : Uint63.of_Z (2 * (lo - Z.of_N (seg_base sg))) = i0) by congruence.
  subst c0. clear H.
  set (base := Z.of_N (seg_base sg)) in *. set (off0 := lo - base) in *.
  assert (I0 : φ i0 = 2 * off0).
  { rewrite <- Ei0. subst off0 base. rewrite Uint63.of_Z_spec, wB_val. apply Z.mod_small. lia. }
  split; [rewrite I0; lia|].
  intros k i' Hk Hi'. rewrite I0 in Hi'.
  set (pc := lo + 4 * Z.of_nat k).
  assert (Hpc : 0 <= pc /\ pc + 4 <= lo + 4 * Z.of_nat n) by (subst pc; lia).
  (* [comment removed for export] *)
  unfold itab_entry, fetch_word.
  assert (Upc : bv_unsigned (Z_to_bv 64 pc) = pc) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
  rewrite Upc.
  replace (negb (pc mod 2 =? 0)) with false.
  2: { symmetry. apply negb_false_iff. apply Z.eqb_eq. subst pc.
       replace (lo + 4 * Z.of_nat k) with ((2 * (lo / 4) + 2 * Z.of_nat k) * 2) by lia. apply Z.mod_mul. lia. }
  unfold code_read. rewrite !Upc. change (Z.of_N 4) with 4.
  rewrite (page_segment_find SEGS lo (4 * Z.of_nat n) sg pc PS) by lia.
  rewrite PERM, SB. change (N.to_nat 4) with 4%nat.
  set (off := Z.to_N (pc - Z.of_N (seg_base sg))).
  assert (Hoff : Z.of_N off = off0 + 4 * Z.of_nat k) by (subst off pc off0 base; rewrite Z2N.id; lia).
  rewrite segment_read4 by lia.
  (* [comment removed for export] *)
  unfold fast_entry.
  pose proof (hexw63_spec c off i' ltac:(lia) ltac:(lia)) as HW. unfold rd4 in HW.
  destruct (hex_byte_at c off) as [b0|]; destruct (hex_byte_at c (off + 1)%N) as [b1|];
    destruct (hex_byte_at c (off + 2)%N) as [b2|]; destruct (hex_byte_at c (off + 3)%N) as [b3|];
    destruct (hexw63 c i') as [z|]; try discriminate HW; try reflexivity.
  assert (HW' : Z_to_bv 32 z = le4 b3 b2 b1 b0) by congruence. cbv zeta. rewrite HW'. reflexivity.
Qed.

Lemma mk_itab_fast_go_sound : forall n pc s i t,
  itab_sound SEGS t ->
  φ i + 8 * Z.of_nat n < 2 ^ 63 ->
  (forall k i', (k < n)%nat -> φ i' = φ i + 8 * Z.of_nat k -> fast_entry s i' = itab_entry SEGS (pc + 4 * Z.of_nat k)) ->
  itab_sound SEGS (mk_itab_fast_go n pc s i t).
Proof.
  induction n as [|n IH]; intros pc s i t Ht Hb Hent; cbn [mk_itab_fast_go]; [exact Ht|].
  pose proof i63_vals as (V1 & V2 & V4 & V6 & V8 & _).
  assert (E0 : fast_entry s i = itab_entry SEGS pc).
  { rewrite <- (Z.add_0_r pc). change 0 with (4 * Z.of_nat 0). apply (Hent 0%nat i); [lia | cbn; lia]. }
  assert (Hi8 : φ (Uint63.add i i63_8) = φ i + 8).
  { rewrite Uint63.add_spec, V8, wB_val. apply Z.mod_small. pose proof (Uint63.to_Z_bounded i). lia. }
  apply IH.
  - destruct pc as [|p|p]; try exact Ht. rewrite E0.
    destruct (itab_entry SEGS (Z.pos p)) as [ins|] eqn:E; [|exact Ht].
    intros pc' i'. unfold itab_lookup. destruct pc' as [|p'|p']; try discriminate.
    destruct (Pos.eq_dec p' p) as [->|Hne].
    + rewrite pt_gss. intros H; injection H as <-. exact E.
    + rewrite pt_gso by exact Hne. exact (Ht (Zpos p') i').
  - rewrite Hi8. lia.
  - intros k i' Hk Hi'. rewrite Hi8 in Hi'.
    replace (pc + 4 + 4 * Z.of_nat k) with (pc + 4 * Z.of_nat (S k)) by lia.
    apply Hent; lia.
Qed.

Lemma mk_itab_page_sound : forall lo n t, itab_sound SEGS t -> itab_sound SEGS (mk_itab_page SEGS lo n t).
Proof.
  intros lo n t Ht. unfold mk_itab_page.
  destruct (page_fast_ok SEGS lo n) as [[c i0]|] eqn:P; [|apply mk_itab_fuel_sound; exact Ht].
  destruct (page_fast_entry lo n c i0 P) as [Hb Hent].
  apply mk_itab_fast_go_sound; [exact Ht | exact Hb | exact Hent].
Qed.

Lemma mk_itab_ranges_fast_acc_sound : forall rs t, itab_sound SEGS t -> itab_sound SEGS (mk_itab_ranges_fast_acc SEGS rs t).
Proof.
  induction rs as [|[lo n] rs IH]; intros t Ht; cbn [mk_itab_ranges_fast_acc]; [exact Ht|].
  apply IH. apply mk_itab_page_sound. exact Ht.
Qed.
Theorem mk_itab_ranges_fast_sound : forall rs, itab_sound SEGS (mk_itab_ranges_fast SEGS rs).
Proof.
  intros rs. rewrite mk_itab_ranges_fast_eq. unfold mk_itab_ranges_fast_ref. apply mk_itab_ranges_fast_acc_sound.
  intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate.
Qed.
End ItabFast.

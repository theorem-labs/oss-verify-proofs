(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Definition nyb (c : char63) : int :=
  if (PrimInt63.leb 48 c && PrimInt63.leb c 57)%bool then PrimInt63.sub c 48
  else if (PrimInt63.leb 97 c && PrimInt63.leb c 102)%bool then PrimInt63.sub c 87 else 16%uint63.

(* [comment removed for export] *)
Definition hbyte (s : PrimString.string) (j : int) : option int :=
  let h := nyb (PrimString.get s j) in
  let l := nyb (PrimString.get s (PrimInt63.add j 1)) in
  if (PrimInt63.ltb h 16 && PrimInt63.ltb l 16)%bool then Some (PrimInt63.add (PrimInt63.mul h 16) l) else None.

(* [comment removed for export] *)
Definition fetch_fast_b (segs : list Segment) (a : Z) (j : int) (pc : w64) : option (bv 32) :=
  match find_segment segs a 4 with
  | Some seg =>
      if (seg_executable seg && negb (seg_writable seg))%bool then
        match seg_bytes seg with
        | [c] =>
            if (2 * (a - Z.of_N (seg_base seg)) + 8 <? 2 ^ 62)%Z && PrimInt63.ltb (PrimInt63.add j 7) (PrimString.length c) then
              match hbyte c j, hbyte c (PrimInt63.add j 2), hbyte c (PrimInt63.add j 4), hbyte c (PrimInt63.add j 6) with
              | Some b0, Some b1, Some b2, Some b3 =>
                  Some (Z_to_bv 32 (Uint63.to_Z
                          (PrimInt63.add b0 (PrimInt63.mul 256 (PrimInt63.add b1 (PrimInt63.mul 256
                             (PrimInt63.add b2 (PrimInt63.mul 256 b3))))))))
              | _, _, _, _ => fetch_word segs (wbv pc)
              end
            else fetch_word segs (wbv pc)
        | _ => fetch_word segs (wbv pc)
        end
      else fetch_word segs (wbv pc)
  | None => fetch_word segs (wbv pc)
  end.

Definition fetch_fast (segs : list Segment) (pc : w64) : option (bv 32) :=
  if wh pc then fetch_word segs (wbv pc) else
  if PrimInt63.eqb (PrimInt63.mod (wl pc) 2) 0 then
    let a := Uint63.to_Z (wl pc) in
    match find_segment segs a 4 with
    | Some seg => fetch_fast_b segs a (Uint63.of_Z (2 * (a - Z.of_N (seg_base seg)))) pc
    | None => fetch_word segs (wbv pc)
    end
  else fetch_word segs (wbv pc).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wB_63 : Uint63Axioms.wB = 2 ^ 63.
Proof. reflexivity. Qed.

Lemma tz_small (z : Z) : 0 <= z < 2 ^ 63 -> Uint63.to_Z (Uint63.of_Z z) = z.
Proof. intros H. rewrite Uint63.of_Z_spec, wB_63. apply Z.mod_small. exact H. Qed.

Lemma tz_add (x y : int) : Uint63.to_Z x + Uint63.to_Z y < 2 ^ 63 ->
  Uint63.to_Z (PrimInt63.add x y) = Uint63.to_Z x + Uint63.to_Z y.
Proof.
  intros H. rewrite Uint63Axioms.add_spec, wB_63. apply Z.mod_small.
  pose proof (Uint63.to_Z_bounded x). pose proof (Uint63.to_Z_bounded y). rewrite ?wB_63 in *. lia.
Qed.

Lemma tz_mul (x y : int) : Uint63.to_Z x * Uint63.to_Z y < 2 ^ 63 ->
  Uint63.to_Z (PrimInt63.mul x y) = Uint63.to_Z x * Uint63.to_Z y.
Proof.
  intros H. rewrite Uint63Axioms.mul_spec, wB_63. apply Z.mod_small.
  pose proof (Uint63.to_Z_bounded x). pose proof (Uint63.to_Z_bounded y). rewrite ?wB_63 in *. nia.
Qed.

Lemma tz_sub (x y : int) : Uint63.to_Z y <= Uint63.to_Z x ->
  Uint63.to_Z (PrimInt63.sub x y) = Uint63.to_Z x - Uint63.to_Z y.
Proof.
  intros H. rewrite Uint63Axioms.sub_spec, wB_63. apply Z.mod_small.
  pose proof (Uint63.to_Z_bounded x). pose proof (Uint63.to_Z_bounded y). rewrite ?wB_63 in *. lia.
Qed.

Lemma nyb_spec (c : char63) : Uint63.to_Z (nyb c) = Z.of_N (hex_nybble c).
Proof.
  unfold nyb, hex_nybble. pose proof (Uint63.to_Z_bounded c) as Bc. rewrite ?wB_63 in Bc.
  destruct (PrimInt63.leb 48 c && PrimInt63.leb c 57)%bool eqn:E1.
  - apply andb_true_iff in E1 as [H1 H2]. apply Uint63Axioms.leb_spec in H1. apply Uint63Axioms.leb_spec in H2.
    change (Uint63Axioms.to_Z 48) with 48 in H1. change (Uint63Axioms.to_Z 57) with 57 in H2.
    rewrite tz_sub by (change (Uint63.to_Z 48) with 48; lia). change (Uint63.to_Z 48) with 48.
    rewrite Z2N.id by lia. reflexivity.
  - destruct (PrimInt63.leb 97 c && PrimInt63.leb c 102)%bool eqn:E2.
    + apply andb_true_iff in E2 as [H1 H2]. apply Uint63Axioms.leb_spec in H1. apply Uint63Axioms.leb_spec in H2.
      change (Uint63Axioms.to_Z 97) with 97 in H1. change (Uint63Axioms.to_Z 102) with 102 in H2.
      rewrite tz_sub by (change (Uint63.to_Z 87) with 87; lia). change (Uint63.to_Z 87) with 87.
      rewrite Z2N.id by lia. reflexivity.
    + reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hex_byte_at_hbyte (s : PrimString.string) (i : N) (v : int) :
  2 * Z.of_N i + 2 <= Uint63.to_Z (PrimString.length s) -> 2 * Z.of_N i + 2 < 2 ^ 62 ->
  hbyte s (Uint63.of_Z (2 * Z.of_N i)) = Some v ->
  hex_byte_at s i = Some (Z_to_bv 8 (Uint63.to_Z v)) /\ Uint63.to_Z v < 256.
Proof.
  intros Hlen Hsm Hb. unfold hbyte in Hb. unfold hex_byte_at.
  replace (Z.of_N (2 * i)) with (2 * Z.of_N i) by lia.
  replace (Z.of_N (2 * i + 1)) with (2 * Z.of_N i + 1) by lia.
  assert (Ej1 : PrimInt63.add (Uint63.of_Z (2 * Z.of_N i)) 1 = Uint63.of_Z (2 * Z.of_N i + 1)).
  { apply Uint63.to_Z_inj. rewrite tz_add; rewrite ?tz_small by lia; change (Uint63.to_Z 1) with 1; lia. }
  rewrite Ej1 in Hb.
  assert (Hlt : PrimInt63.ltb (Uint63.of_Z (2 * Z.of_N i + 1)) (PrimString.length s) = true).
  { apply Uint63Axioms.ltb_spec. rewrite tz_small by lia. lia. }
  change Uint63.ltb with PrimInt63.ltb. rewrite Hlt. cbn [orb].
  set (ch := PrimString.get s (Uint63.of_Z (2 * Z.of_N i))) in *.
  set (cl := PrimString.get s (Uint63.of_Z (2 * Z.of_N i + 1))) in *.
  destruct (PrimInt63.ltb (nyb ch) 16 && PrimInt63.ltb (nyb cl) 16)%bool eqn:E; [|discriminate].
  injection Hb as <-. apply andb_true_iff in E as [E1 E2].
  apply Uint63Axioms.ltb_spec in E1. apply Uint63Axioms.ltb_spec in E2.
  change (Uint63Axioms.to_Z 16) with 16 in E1, E2. change (Uint63Axioms.to_Z) with Uint63.to_Z in E1, E2.
  rewrite !nyb_spec in E1, E2.
  assert (Eh : (hex_nybble ch <? 16)%N = true) by (apply N.ltb_lt; lia).
  assert (El : (hex_nybble cl <? 16)%N = true) by (apply N.ltb_lt; lia).
  rewrite Eh, El. cbn [andb].
  assert (Ev : Uint63.to_Z (PrimInt63.add (PrimInt63.mul (nyb ch) 16) (nyb cl)) = Z.of_N (hex_nybble ch * 16 + hex_nybble cl)).
  { rewrite tz_add; rewrite ?tz_mul; change (Uint63.to_Z 16) with 16; rewrite ?nyb_spec; lia. }
  rewrite Ev. split; [reflexivity | lia].
Qed.

Lemma land_low_high (a b k : Z) : 0 <= a < 2 ^ k -> 0 <= b -> 0 <= k -> Z.land (b * 2 ^ k) a = 0.
Proof.
  intros Ha Hb Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n k) as [L|G].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.eq_dec a 0) as [->|Hnz]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 a n); [apply andb_false_r | lia |].
    apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_shift_add (a b k : Z) : 0 <= a < 2 ^ k -> 0 <= b -> 0 <= k -> Z.lor (b * 2 ^ k) a = b * 2 ^ k + a.
Proof.
  intros Ha Hb Hk. rewrite <- Z.lxor_lor by (apply land_low_high; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_low_high; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le4_val (x0 x1 x2 x3 : Z) :
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  le4 (Z_to_bv 8 x3) (Z_to_bv 8 x2) (Z_to_bv 8 x1) (Z_to_bv 8 x0) = Z_to_bv 32 (x0 + 256 * (x1 + 256 * (x2 + 256 * x3))).
Proof.
  intros H0 H1 H2 H3. apply bv_eq. unfold le4, le2.
  rewrite (bv_concat_unsigned 32 16 (bv_concat 16 (Z_to_bv 8 x3) (Z_to_bv 8 x2)) (bv_concat 16 (Z_to_bv 8 x1) (Z_to_bv 8 x0))) by reflexivity.
  rewrite !(bv_concat_unsigned 16 8) by reflexivity. rewrite !Z_to_bv_unsigned.
  rewrite !(bv_wrap_small 8) by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia).
  rewrite (bv_wrap_small 32) by (unfold bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; lia).
  change (Z.of_N 8) with 8. change (Z.of_N 16) with 16.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (lor_shift_add x2 x3 8) by (change (2 ^ 8) with 256; lia).
  rewrite (lor_shift_add x0 x1 8) by (change (2 ^ 8) with 256; lia).
  rewrite (lor_shift_add (x1 * 2 ^ 8 + x0) (x3 * 2 ^ 8 + x2) 16) by (change (2 ^ 8) with 256; change (2 ^ 16) with 65536; lia).
  change (2 ^ 8) with 256. change (2 ^ 16) with 65536. lia.
Qed.

Lemma find_segment_range (segs : list Segment) (a n : Z) (seg : Segment) :
  find_segment segs a n = Some seg -> Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|sg rest IH]; intros H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:E.
  - injection H as <-. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  - exact (IH H).
Qed.

(* [comment removed for export] *)
Lemma seg_byte_fast (c : PrimString.string) (off : Z) (k : Z) (v : int) :
  0 <= off -> 0 <= k <= 3 -> 2 * off + 8 < 2 ^ 62 -> 2 * off + 8 <= Uint63.to_Z (PrimString.length c) ->
  hbyte c (PrimInt63.add (Uint63.of_Z (2 * off)) (Uint63.of_Z (2 * k))) = Some v ->
  segment_byte_at [c] (Z.to_N (off + k)) = Some (Z_to_bv 8 (Uint63.to_Z v)) /\ Uint63.to_Z v < 256.
Proof.
  intros Ho Hk Hs Hl Hb. pose proof (Uint63.to_Z_bounded (PrimString.length c)) as Bl. rewrite ?wB_63 in Bl.
  cbn [segment_byte_at].
  assert (Hc : (Z.to_N (off + k) <? Z.to_N (Uint63.to_Z (PrimString.length c) / 2))%N = true).
  { apply N.ltb_lt. apply Z2N.inj_lt; [lia | apply Z.div_pos; lia |].
    apply (Z.lt_le_trans _ (off + 4)); [lia|]. apply Z.div_le_lower_bound; lia. }
  rewrite Hc.
  replace (PrimInt63.add (Uint63.of_Z (2 * off)) (Uint63.of_Z (2 * k))) with (Uint63.of_Z (2 * Z.of_N (Z.to_N (off + k)))) in Hb.
  - apply hex_byte_at_hbyte; [rewrite Z2N.id by lia; lia | rewrite Z2N.id by lia; lia | exact Hb].
  - apply Uint63.to_Z_inj. rewrite Z2N.id by lia. rewrite tz_add; rewrite ?tz_small by lia; lia.
Qed.

Theorem fetch_fast_eq (segs : list Segment) (pc : w64) : fetch_fast segs pc = fetch_word segs (wbv pc).
Proof.
  unfold fetch_fast. destruct (wh pc) eqn:Ewh; [reflexivity|].
  destruct (PrimInt63.eqb (PrimInt63.mod (wl pc) 2) 0) eqn:Eal; [|reflexivity].
  cbv zeta.
  destruct (find_segment segs (Uint63.to_Z (wl pc)) 4) as [seg|] eqn:Ef; [|reflexivity].
  unfold fetch_fast_b. rewrite Ef.
  destruct (seg_executable seg && negb (seg_writable seg))%bool eqn:Ex; [|reflexivity].
  destruct (seg_bytes seg) as [|c [|c' rest]] eqn:Eb; try reflexivity.
  set (a := Uint63.to_Z (wl pc)) in *.
  set (off := a - Z.of_N (seg_base seg)) in *.
  destruct ((2 * off + 8 <? 2 ^ 62) && PrimInt63.ltb (PrimInt63.add (Uint63.of_Z (2 * off)) 7) (PrimString.length c))%bool eqn:Eb2;
    [|reflexivity].
  destruct (hbyte c (Uint63.of_Z (2 * off))) as [b0|] eqn:B0; [|reflexivity].
  destruct (hbyte c (PrimInt63.add (Uint63.of_Z (2 * off)) 2)) as [b1|] eqn:B1; [|reflexivity].
  destruct (hbyte c (PrimInt63.add (Uint63.of_Z (2 * off)) 4)) as [b2|] eqn:B2; [|reflexivity].
  destruct (hbyte c (PrimInt63.add (Uint63.of_Z (2 * off)) 6)) as [b3|] eqn:B3; [|reflexivity].
  symmetry.
  pose proof (find_segment_range segs a 4 seg Ef) as [R1 R2].
  apply andb_true_iff in Eb2 as [Es Elt]. apply Z.ltb_lt in Es. apply Uint63Axioms.ltb_spec in Elt.
  pose proof (Uint63.to_Z_bounded (wl pc)) as Ba. rewrite ?wB_63 in Ba.
  assert (Hj : Uint63.to_Z (Uint63.of_Z (2 * off)) = 2 * off) by (apply tz_small; lia).
  change Uint63Axioms.to_Z with Uint63.to_Z in Elt.
  rewrite tz_add in Elt by (rewrite Hj; change (Uint63.to_Z 7) with 7; lia).
  rewrite Hj in Elt. change (Uint63.to_Z 7) with 7 in Elt.
  assert (Hb : forall k v, 0 <= k <= 3 -> hbyte c (PrimInt63.add (Uint63.of_Z (2 * off)) (Uint63.of_Z (2 * k))) = Some v ->
      segment_byte_at [c] (Z.to_N (off + k)) = Some (Z_to_bv 8 (Uint63.to_Z v)) /\ Uint63.to_Z v < 256)
    by (intros k v Hk Hv; apply seg_byte_fast; [lia | lia | lia | lia | exact Hv]).
  assert (E0 : PrimInt63.add (Uint63.of_Z (2 * off)) (Uint63.of_Z (2 * 0)) = Uint63.of_Z (2 * off)).
  { apply Uint63.to_Z_inj. rewrite tz_add; rewrite ?Hj; change (Uint63.to_Z (Uint63.of_Z (2 * 0))) with 0; lia. }
  destruct (Hb 0 b0 ltac:(lia) ltac:(rewrite E0; exact B0)) as [S0 V0].
  destruct (Hb 1 b1 ltac:(lia) ltac:(change (Uint63.of_Z (2 * 1)) with 2%uint63; exact B1)) as [S1 V1].
  destruct (Hb 2 b2 ltac:(lia) ltac:(change (Uint63.of_Z (2 * 2)) with 4%uint63; exact B2)) as [S2 V2].
  destruct (Hb 3 b3 ltac:(lia) ltac:(change (Uint63.of_Z (2 * 3)) with 6%uint63; exact B3)) as [S3 V3].
  clear Hb E0.
  pose proof (Uint63.to_Z_bounded b0). pose proof (Uint63.to_Z_bounded b1).
  pose proof (Uint63.to_Z_bounded b2). pose proof (Uint63.to_Z_bounded b3).
  unfold fetch_word, code_read.
  rewrite wbv_unsigned.
  assert (Ew : wZ pc = a) by (unfold wZ; rewrite Ewh; reflexivity).
  rewrite Ew.
  assert (Hal : a mod 2 = 0).
  { apply Uint63.eqb_spec in Eal. apply (f_equal Uint63.to_Z) in Eal. rewrite Uint63Axioms.mod_spec in Eal. exact Eal. }
  rewrite Hal. cbn [Z.eqb negb].
  change (Z.of_N 4) with 4. rewrite Ef, Ex, Eb.
  change (N.to_nat 4) with 4%nat.
  cbn [segment_read_bytes].
  replace (Z.to_N (off + 0)) with (Z.to_N (a - Z.of_N (seg_base seg))) in S0 by (unfold off; f_equal; lia).
  replace (Z.to_N (off + 1)) with (Z.to_N (a - Z.of_N (seg_base seg)) + 1)%N in S1 by (unfold off; lia).
  replace (Z.to_N (off + 2)) with (Z.to_N (a - Z.of_N (seg_base seg)) + 1 + 1)%N in S2 by (unfold off; lia).
  replace (Z.to_N (off + 3)) with (Z.to_N (a - Z.of_N (seg_base seg)) + 1 + 1 + 1)%N in S3 by (unfold off; lia).
  rewrite S0, S1, S2, S3. f_equal.
  rewrite le4_val by lia. f_equal.
  assert (T3 : Uint63.to_Z (PrimInt63.mul 256 b3) = 256 * Uint63.to_Z b3)
    by (rewrite tz_mul; change (Uint63.to_Z 256) with 256; lia).
  assert (T2 : Uint63.to_Z (PrimInt63.add b2 (PrimInt63.mul 256 b3)) = Uint63.to_Z b2 + 256 * Uint63.to_Z b3)
    by (rewrite tz_add; rewrite T3; lia).
  assert (T2' : Uint63.to_Z (PrimInt63.mul 256 (PrimInt63.add b2 (PrimInt63.mul 256 b3))) = 256 * (Uint63.to_Z b2 + 256 * Uint63.to_Z b3))
    by (rewrite tz_mul; change (Uint63.to_Z 256) with 256; rewrite T2; lia).
  assert (T1 : Uint63.to_Z (PrimInt63.add b1 (PrimInt63.mul 256 (PrimInt63.add b2 (PrimInt63.mul 256 b3))))
               = Uint63.to_Z b1 + 256 * (Uint63.to_Z b2 + 256 * Uint63.to_Z b3))
    by (rewrite tz_add; rewrite T2'; lia).
  assert (T1' : Uint63.to_Z (PrimInt63.mul 256 (PrimInt63.add b1 (PrimInt63.mul 256 (PrimInt63.add b2 (PrimInt63.mul 256 b3)))))
               = 256 * (Uint63.to_Z b1 + 256 * (Uint63.to_Z b2 + 256 * Uint63.to_Z b3)))
    by (rewrite tz_mul; change (Uint63.to_Z 256) with 256; rewrite T1; lia).
  rewrite tz_add; rewrite T1'; lia.
Qed.

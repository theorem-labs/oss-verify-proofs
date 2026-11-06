(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec Mem.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie AxFetchFast AxFetchFast2.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition asm8 (b0 b1 b2 b3 b4 b5 b6 b7 : int) : w64 :=
  W (128 <=? b7)%uint63
    (b0 lor (b1 << 8) lor (b2 << 16) lor (b3 << 24) lor (b4 << 32) lor (b5 << 40) lor (b6 << 48) lor ((b7 land 127) << 56))%uint63.

Lemma shl_small (b k : int) (bound : Z) : to_Z k <= 56 -> to_Z b < bound -> bound * 2 ^ to_Z k <= 2 ^ 63 -> to_Z (b << k)%uint63 = to_Z b * 2 ^ to_Z k.
Proof.
  intros Hk Hb Hbd. pose proof (to_Z_bounded b) as Bb. pose proof (to_Z_bounded k) as Bk. rewrite lsl_spec.
  apply Z.mod_small. rewrite wB_eq. unfold two63. assert (0 < 2 ^ to_Z k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.mul_nonneg_nonneg; lia|]. apply (Z.lt_le_trans _ (bound * 2 ^ to_Z k)); [apply Z.mul_lt_mono_pos_r; lia | exact Hbd].
Qed.

Lemma lor_add (a b k : Z) : 0 <= a < 2 ^ k -> 0 <= b -> 0 <= k -> Z.lor a (b * 2 ^ k) = a + b * 2 ^ k.
Proof. intros Ha Hb Hk. rewrite Z.lor_comm. rewrite lor_shift_add by assumption. ring. Qed.

Lemma wZ_asm8 (b0 b1 b2 b3 b4 b5 b6 b7 : int) :
  to_Z b0 < 256 -> to_Z b1 < 256 -> to_Z b2 < 256 -> to_Z b3 < 256 -> to_Z b4 < 256 -> to_Z b5 < 256 -> to_Z b6 < 256 -> to_Z b7 < 256 ->
  wZ (asm8 b0 b1 b2 b3 b4 b5 b6 b7)
  = to_Z b0 + 2 ^ 8 * to_Z b1 + 2 ^ 16 * to_Z b2 + 2 ^ 24 * to_Z b3 + 2 ^ 32 * to_Z b4 + 2 ^ 40 * to_Z b5 + 2 ^ 48 * to_Z b6 + 2 ^ 56 * to_Z b7.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7.
  pose proof (to_Z_bounded b0). pose proof (to_Z_bounded b1). pose proof (to_Z_bounded b2). pose proof (to_Z_bounded b3).
  pose proof (to_Z_bounded b4). pose proof (to_Z_bounded b5). pose proof (to_Z_bounded b6). pose proof (to_Z_bounded b7).
  assert (E7 : to_Z (b7 land 127)%uint63 = to_Z b7 mod 128).
  { rewrite land_spec'. change (to_Z 127%uint63) with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. }
  assert (L7 : to_Z (b7 land 127)%uint63 < 256) by (rewrite E7; pose proof (Z.mod_pos_bound (to_Z b7) 128 ltac:(lia)); lia).
  unfold asm8, wZ. cbn [wh wl]. rewrite !lor_spec'.
  assert (L7' : to_Z (b7 land 127)%uint63 < 128) by (rewrite E7; pose proof (Z.mod_pos_bound (to_Z b7) 128 ltac:(lia)); lia).
  rewrite (shl_small b1 8 256), (shl_small b2 16 256), (shl_small b3 24 256), (shl_small b4 32 256), (shl_small b5 40 256), (shl_small b6 48 256),
          (shl_small (b7 land 127)%uint63 56 128) by (first [assumption | (vm_compute; discriminate)]).
  change (to_Z 8%uint63) with 8. change (to_Z 16%uint63) with 16. change (to_Z 24%uint63) with 24. change (to_Z 32%uint63) with 32.
  change (to_Z 40%uint63) with 40. change (to_Z 48%uint63) with 48. change (to_Z 56%uint63) with 56.
  rewrite (lor_add (to_Z b0) (to_Z b1) 8) by lia.
  rewrite (lor_add _ (to_Z b2) 16) by lia.
  rewrite (lor_add _ (to_Z b3) 24) by lia.
  rewrite (lor_add _ (to_Z b4) 32) by lia.
  rewrite (lor_add _ (to_Z b5) 40) by lia.
  rewrite (lor_add _ (to_Z b6) 48) by lia.
  rewrite (lor_add _ (to_Z (b7 land 127)%uint63) 56) by (pose proof (to_Z_bounded (b7 land 127)%uint63); lia).
  rewrite E7. unfold two63.
  destruct (128 <=? b7)%uint63 eqn:E; [apply leb_spec in E | apply Bool.not_true_iff_false in E; rewrite leb_spec in E];
    change (to_Z 128%uint63) with 128 in E; pose proof (Z.div_mod (to_Z b7) 128 ltac:(lia)); pose proof (Z.mod_pos_bound (to_Z b7) 128 ltac:(lia));
    assert (to_Z b7 / 128 = 1 \/ to_Z b7 / 128 = 0) by lia; lia.
Qed.

Lemma byteZ_sum8 (z0 z1 z2 z3 z4 z5 z6 z7 j : Z) :
  0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 -> 0 <= z4 < 256 -> 0 <= z5 < 256 -> 0 <= z6 < 256 -> 0 <= z7 < 256 ->
  0 <= j < 8 ->
  byteZ (z0 + 2 ^ 8 * z1 + 2 ^ 16 * z2 + 2 ^ 24 * z3 + 2 ^ 32 * z4 + 2 ^ 40 * z5 + 2 ^ 48 * z6 + 2 ^ 56 * z7) j
  = nth (Z.to_nat j) [z0; z1; z2; z3; z4; z5; z6; z7] 0.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 Hj. unfold byteZ.
  assert (C : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; simpl (nth _ _ _);
    match goal with |- (_ / 2 ^ ?e) mod 256 = _ => let v := eval compute in (2 ^ e) in change (2 ^ e) with v end;
    change (2 ^ 8) with 256; change (2 ^ 16) with 65536; change (2 ^ 24) with 16777216; change (2 ^ 32) with 4294967296;
    change (2 ^ 40) with 1099511627776; change (2 ^ 48) with 281474976710656; change (2 ^ 56) with 72057594037927936;
    Z.div_mod_to_equations; lia.
Qed.

Fixpoint img_valid (c : string) (x : int) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S n => match hbyte c (x << 1)%uint63 with Some _ => img_valid c (x + 1)%uint63 n | None => false end
  end.

Lemma img_valid_spec (c : string) : forall (cnt : nat) (x y : int),
  img_valid c x cnt = true -> to_Z x + Z.of_nat cnt < 2 ^ 60 -> to_Z x <= to_Z y < to_Z x + Z.of_nat cnt ->
  exists v, hbyte c (y << 1)%uint63 = Some v.
Proof.
  induction cnt as [|cnt IH]; intros x y H Hb Hy; [lia|]. cbn [img_valid] in H.
  destruct (hbyte c (x << 1)%uint63) as [v|] eqn:E; [|discriminate].
  pose proof (to_Z_bounded x) as Bx.
  assert (E1 : to_Z (x + 1)%uint63 = to_Z x + 1) by (rewrite add_spec; change (to_Z 1%uint63) with 1; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
  destruct (Z.eq_dec (to_Z y) (to_Z x)) as [Ey|Ey].
  - apply to_Z_inj in Ey. subst y. exists v. exact E.
  - apply (IH (x + 1)%uint63 y H); rewrite E1; lia.
Qed.

Lemma uadd_0_r (x : int) : (x + 0)%uint63 = x.
Proof. apply to_Z_inj. rewrite add_spec. change (to_Z 0%uint63) with 0. rewrite Z.add_0_r. apply Z.mod_small. apply to_Z_bounded. Qed.

Section Img.
Variable segs : list Segment.

Lemma img_byte_spec (i : nat) (sg : Segment) (c : string) (x v : int) :
  nth_error segs i = Some sg -> seg_bytes sg = [c] -> img_byte segs i x = Some v ->
  2 * to_Z x + 2 <= to_Z (PrimString.length c) -> to_Z x < 2 ^ 60 ->
  segment_byte_at (seg_bytes sg) (Z.to_N (to_Z x)) = Some (Z_to_bv 8 (to_Z v)) /\ to_Z v < 256.
Proof.
  intros Hn Hc Hb Hlen Hx. unfold img_byte in Hb. rewrite Hn, Hc in Hb. rewrite Hc. pose proof (to_Z_bounded x) as Bx.
  assert (Ex : (x << 1)%uint63 = of_Z (2 * Z.of_N (Z.to_N (to_Z x)))).
  { apply to_Z_inj. rewrite lsl_spec, of_Z_spec, Z2N.id by lia. change (2 ^ to_Z 1%uint63) with 2. rewrite (Z.mul_comm (to_Z x)). reflexivity. }
  rewrite Ex in Hb. cbn [segment_byte_at].
  assert (Hlt : (Z.to_N (to_Z x) <? Z.to_N (to_Z (PrimString.length c) / 2))%N = true).
  { apply N.ltb_lt. apply Z2N.inj_lt; [lia | apply Z.div_pos; lia |]. apply (Z.lt_le_trans _ (to_Z x + 1)); [lia|]. apply Z.div_le_lower_bound; lia. }
  rewrite Hlt. apply hex_byte_at_hbyte; [rewrite Z2N.id by lia; lia | rewrite Z2N.id by lia; lia | exact Hb].
Qed.

Lemma img_region_ok (rho : valuation) (t : int) (lo size al : int) (wr : bool) (i : nat) (dl : int) (d : nat)
    (sg : Segment) (c : string) (m : word -> option byte) :
  nth_error segs i = Some sg -> seg_bytes sg = [c] -> seg_readable sg = true -> (wr = true -> seg_writable sg = true) ->
  to_Z lo = Z.of_N (seg_base sg) + to_Z dl ->
  (forall a, to_Z lo <= a < to_Z lo + to_Z size -> find_segment segs a 1 = Some sg) ->
  2 * (to_Z dl + to_Z size) <= to_Z (PrimString.length c) -> to_Z dl + to_Z size < 2 ^ 59 ->
  img_valid c dl (Z.to_nat (to_Z size)) = true ->
  (forall a, to_Z lo <= a < to_Z lo + to_Z size -> m (wa a) = None) ->
  0 < to_Z lo -> to_Z lo + to_Z size < two63 -> to_Z size <= 8 * 2 ^ Z.of_nat d -> Z.of_nat d <= 59 ->
  to_Z al < 63 -> to_Z lo mod 2 ^ to_Z al = 0 ->
  region_ok segs rho t (RG (Some lo) size al wr (DImage i dl) d IEmpty) m.
Proof.
  intros Hn Hc Hrd Hwr Elo Hseg Hlen H59 Hval Hnone Hpos Hhi Hd Hd59 Hal Hmod.
  pose proof (to_Z_bounded dl) as Bdl. pose proof (to_Z_bounded size) as Bsz. pose proof (to_Z_bounded lo) as Blo.
  unfold region_ok, rbase. cbn [rg_abs rg_size rg_al rg_wr rg_d].
  split; [split; [lia | left; exact Hpos]|]. split; [exact Hhi|]. split; [lia|]. split; [exact Hd|]. split; [exact Hd59|]. split; [exact Hal|]. split; [exact Hmod|].
  intros k Hk. unfold two63 in Hhi.

  assert (Exk : to_Z (dl + of_Z k)%uint63 = to_Z dl + k).
  { rewrite add_spec, of_Z_spec. rewrite (Z.mod_small k) by (rewrite wB_eq; unfold two63; lia). apply Z.mod_small. rewrite wB_eq. unfold two63. lia. }
  destruct (img_valid_spec c (Z.to_nat (to_Z size)) dl (dl + of_Z k)%uint63 Hval ltac:(rewrite Z2Nat.id by lia; lia) ltac:(rewrite Exk, Z2Nat.id by lia; lia)) as [v Hv].
  assert (Hib : img_byte segs i (dl + of_Z k)%uint63 = Some v) by (unfold img_byte; rewrite Hn, Hc; exact Hv).
  destruct (img_byte_spec i sg c _ v Hn Hc Hib ltac:(rewrite Exk; lia) ltac:(rewrite Exk; lia)) as [Hsb Hv256].
  rewrite Exk in Hsb.
  assert (Ha : bv_unsigned (wa (to_Z lo + k)) = to_Z lo + k) by (apply wa_unsigned; lia).
  assert (Hoff : Z.to_N (to_Z lo + k - Z.of_N (seg_base sg)) = Z.to_N (to_Z dl + k)) by (rewrite Elo; f_equal; lia).
  assert (Hrom : seg_rom segs (wa (to_Z lo + k)) = Some (Z_to_bv 8 (to_Z v))).
  { unfold seg_rom, memory_read. rewrite Ha. change (Z.of_N 1) with 1. rewrite (Hseg (to_Z lo + k) ltac:(lia)), Hrd.
    rewrite Hoff. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite Hsb. reflexivity. }
  exists (Z_to_bv 8 (to_Z v)). split; [unfold mrd; rewrite (Hnone (to_Z lo + k) ltac:(lia)); exact Hrom|]. split.
  -
    unfold rg_kb, rd_cell. cbn [rg_d rg_cells rg_dflt]. rewrite iget_empty. cbn [dflt_cell]. unfold img_cell.
    pose proof (Z.div_mod k 8 ltac:(lia)) as Ek8. pose proof (Z.mod_pos_bound k 8 ltac:(lia)) as Hk8.
    set (x0 := (dl + (of_Z (k / 8) << 3))%uint63).
    assert (Ex0 : to_Z x0 = to_Z dl + 8 * (k / 8)).
    { unfold x0. rewrite add_spec, lsl_spec, of_Z_spec. change (2 ^ to_Z 3%uint63) with 8.
      assert (0 <= k / 8) by (apply Z.div_pos; lia). assert (k / 8 <= k) by (apply Z.div_le_upper_bound; lia).
      rewrite (Z.mod_small (k / 8)) by (rewrite wB_eq; unfold two63; lia). rewrite (Z.mod_small (k / 8 * 8)) by (rewrite wB_eq; unfold two63; lia).
      rewrite Z.mod_small by (rewrite wB_eq; unfold two63; lia). lia. }
    destruct (img_byte segs i x0) as [b0|] eqn:E0; [|cbn [cell_kb]; change (to_Z 0%uint63) with 0; rewrite Z.bits_0; exact I].
    destruct (img_byte segs i (x0 + 1)%uint63) as [b1|] eqn:E1; [|cbn [cell_kb]; change (to_Z 0%uint63) with 0; rewrite Z.bits_0; exact I].
    destruct (img_byte segs i (x0 + 2)%uint63) as [b2|] eqn:E2; [|cbn [cell_kb]; change (to_Z 0%uint63) with 0; rewrite Z.bits_0; exact I].
    destruct (img_byte segs i (x0 + 3)%uint63) as [b3|] eqn:E3; [|cbn [cell_kb]; change (to_Z 0%uint63) with 0; rewrite Z.bits_0; exact I].
    destruct (img_byte segs i (x0 + 4)%uint63) as [b4|] eqn:E4; [|cbn [cell_kb]; change (to_Z 0%uint63) with 0; rewrite Z.bits_0; exact I].
    destruct (img_byte segs i (x0 + 5)%uint63) as [b5|] eqn:E5; [|cbn [cell_kb]; change (to_Z 0%uint63) with 0; rewrite Z.bits_0; exact I].
    destruct (img_byte segs i (x0 + 6)%uint63) as [b6|] eqn:E6; [|cbn [cell_kb]; change (to_Z 0%uint63) with 0; rewrite Z.bits_0; exact I].
    destruct (img_byte segs i (x0 + 7)%uint63) as [b7|] eqn:E7; [|cbn [cell_kb]; change (to_Z 0%uint63) with 0; rewrite Z.bits_0; exact I].
    fold (asm8 b0 b1 b2 b3 b4 b5 b6 b7). cbn [cell_kb]. change (to_Z 255%uint63) with 255. rewrite testbit_255 by lia. cbn [kb_ok].

    assert (HB : forall (j : Z) (bj : int), 0 <= j < 8 -> img_byte segs i (x0 + of_Z j)%uint63 = Some bj -> to_Z bj < 256).
    { intros j bj Hj Hbj. unfold img_byte in Hbj. rewrite Hn, Hc in Hbj. exact (hbyte_lt _ _ _ Hbj). }
    pose proof (HB 0 b0 ltac:(lia) ltac:(change (of_Z 0) with 0%uint63; rewrite uadd_0_r; exact E0)) as L0.
    pose proof (HB 1 b1 ltac:(lia) E1) as L1. pose proof (HB 2 b2 ltac:(lia) E2) as L2. pose proof (HB 3 b3 ltac:(lia) E3) as L3.
    pose proof (HB 4 b4 ltac:(lia) E4) as L4. pose proof (HB 5 b5 ltac:(lia) E5) as L5. pose proof (HB 6 b6 ltac:(lia) E6) as L6.
    pose proof (HB 7 b7 ltac:(lia) E7) as L7.
    rewrite wZ_asm8 by assumption.
    pose proof (to_Z_bounded b0). pose proof (to_Z_bounded b1). pose proof (to_Z_bounded b2). pose proof (to_Z_bounded b3).
    pose proof (to_Z_bounded b4). pose proof (to_Z_bounded b5). pose proof (to_Z_bounded b6). pose proof (to_Z_bounded b7).
    rewrite byteZ_sum8 by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; pose proof (to_Z_bounded v); lia).

    assert (Exj : (dl + of_Z k)%uint63 = (x0 + of_Z (k mod 8))%uint63).
    { apply to_Z_inj. rewrite Exk. rewrite add_spec, Ex0, of_Z_spec. rewrite (Z.mod_small (k mod 8)) by (rewrite wB_eq; unfold two63; lia).
      rewrite Z.mod_small by (rewrite wB_eq; unfold two63; lia). lia. }
    rewrite Exj in Hib.
    assert (C : k mod 8 = 0 \/ k mod 8 = 1 \/ k mod 8 = 2 \/ k mod 8 = 3 \/ k mod 8 = 4 \/ k mod 8 = 5 \/ k mod 8 = 6 \/ k mod 8 = 7) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; rewrite C in Hib |- *; simpl (nth _ _ _);
      [change (of_Z 0) with 0%uint63 in Hib; rewrite uadd_0_r in Hib | change (of_Z 1) with 1%uint63 in Hib | change (of_Z 2) with 2%uint63 in Hib
      | change (of_Z 3) with 3%uint63 in Hib | change (of_Z 4) with 4%uint63 in Hib | change (of_Z 5) with 5%uint63 in Hib
      | change (of_Z 6) with 6%uint63 in Hib | change (of_Z 7) with 7%uint63 in Hib ]; congruence.
  - intros Hw. unfold wview. rewrite (Hnone (to_Z lo + k) ltac:(lia)). rewrite Ha, (Hseg (to_Z lo + k) ltac:(lia)), (Hwr Hw).
    rewrite Hoff, Hsb. discriminate.
Qed.

End Img.

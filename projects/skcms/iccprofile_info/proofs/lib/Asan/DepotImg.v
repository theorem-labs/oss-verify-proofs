(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimString PrimStringAxioms Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Abbreviation SEGS := Asan.M.loaded_segments.
Definition SEG3 : Segment := Asan_segment_003.
Definition CH3 : PrimString.string := Asan_seg_bytes_003.
Definition B3 : Z := 0xa0000.
Definition DEP_D : Z := 0x188a98.
Definition DEP_SS : Z := 0x178a88.
Definition LEN_D : Z := 0x400018.
Definition LEN_S : Z := 32.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma chunk_zero_d : PrimString.sub CH3 (of_Z (2 * (DEP_D - B3))) (of_Z (2 * LEN_D)) = PrimString.make (of_Z (2 * LEN_D)) 48%uint63.
Proof. vm_cast_no_check (@eq_refl PrimString.string (PrimString.make (of_Z (2 * LEN_D)) 48%uint63)). Qed.
Lemma chunk_zero_s : PrimString.sub CH3 (of_Z (2 * (DEP_SS - B3))) (of_Z (2 * LEN_S)) = PrimString.make (of_Z (2 * LEN_S)) 48%uint63.
Proof. vm_cast_no_check (@eq_refl PrimString.string (PrimString.make (of_Z (2 * LEN_S)) 48%uint63)). Qed.
Lemma CH3_length : to_Z (PrimString.length CH3) = 2 * 0x55c000.
Proof. vm_compute. reflexivity. Qed.

Lemma nth_firstn_skipn : forall {T} (l : list T) o n i d, (i < n)%nat -> (o + n <= length l)%nat ->
  nth i (firstn n (skipn o l)) d = nth (o + i) l d.
Proof.
  intros T l o n i d Hi Hl. rewrite nth_firstn. destruct (Nat.ltb_spec i n); [|lia]. cbn [andb].
  rewrite nth_skipn. reflexivity.
Qed.

Lemma nth_repeat' : forall {T} (c d : T) n i, (i < n)%nat -> nth i (repeat c n) d = c.
Proof. intros T c d n. induction n as [|n IH]; intros i Hi; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [repeat nth]. apply IH. lia. Qed.

(* [comment removed for export] *)
Lemma get_zero_gen : forall (c : PrimString.string) off len, 0 <= off -> 0 < len -> 2 * off + 2 * len <= to_Z (PrimString.length c) ->
  to_Z (PrimString.length c) < 16777211 ->
  PrimString.sub c (of_Z (2 * off)) (of_Z (2 * len)) = PrimString.make (of_Z (2 * len)) 48%uint63 ->
  forall j, 2 * off <= j < 2 * off + 2 * len -> PrimString.get c (of_Z j) = 48%uint63.
Proof.
  intros c off len Ho Hl Hb HL16 Hz j Hj.
  assert (Hw : 16777211 < wB) by (vm_compute; reflexivity).
  assert (HM : to_Z max_length = 16777211) by (vm_compute; reflexivity).
  apply (f_equal to_list) in Hz. rewrite PrimStringAxioms.sub_spec, PrimStringAxioms.make_spec in Hz.
  rewrite PrimStringAxioms.get_spec.
  match type of Hz with ListDef.firstn ?N (ListDef.skipn ?O _) = ListDef.repeat ?C ?N2 =>
    set (n2 := N2) in *; set (cc := C) in *; set (o := O) in *; set (n := N) in * end.
  assert (Eo : o = Z.to_nat (2 * off)) by (subst o; rewrite of_Z_spec, Z.mod_small by lia; reflexivity).
  assert (En : n = Z.to_nat (2 * len)) by (subst n; rewrite of_Z_spec, Z.mod_small by lia; reflexivity).
  assert (En2 : n2 = n) by (subst n2 n; rewrite of_Z_spec, Z.mod_small by lia; rewrite HM; apply Nat.min_l; lia).
  assert (Ec : cc = 48%uint63) by (subst cc; vm_compute; reflexivity).
  rewrite En2, Ec in Hz.
  match goal with |- ListDef.nth ?I _ _ = _ => set (ii := I) end.
  assert (Ei : ii = Z.to_nat j) by (subst ii; rewrite of_Z_spec, Z.mod_small by lia; reflexivity).
  rewrite Ei.
  assert (Hlen : (o + n <= List.length (to_list c))%nat).
  { rewrite <- PrimStringAxioms.length_spec. rewrite Eo, En. lia. }
  assert (Hi : (Z.to_nat j - o < n)%nat) by (rewrite Eo, En; lia).
  pose proof (f_equal (fun l : list char63 => @ListDef.nth char63 (Z.to_nat j - o) l 0%uint63) Hz) as X. cbn beta in X.
  rewrite (nth_firstn_skipn (to_list c) o n (Z.to_nat j - o) 0%uint63 Hi Hlen) in X. rewrite nth_repeat' in X by exact Hi.
  replace (o + (Z.to_nat j - o))%nat with (Z.to_nat j) in X by (rewrite Eo; lia).
  exact X.
Qed.

Lemma get_zero_d : forall j, 2 * (DEP_D - B3) <= j < 2 * (DEP_D - B3) + 2 * LEN_D -> PrimString.get CH3 (of_Z j) = 48%uint63.
Proof.
  apply (get_zero_gen CH3 (DEP_D - B3) LEN_D); [unfold DEP_D, B3; lia | unfold LEN_D; lia | | | exact chunk_zero_d];
    rewrite CH3_length; unfold DEP_D, B3, LEN_D; lia.
Qed.
Lemma get_zero_s : forall j, 2 * (DEP_SS - B3) <= j < 2 * (DEP_SS - B3) + 2 * LEN_S -> PrimString.get CH3 (of_Z j) = 48%uint63.
Proof.
  apply (get_zero_gen CH3 (DEP_SS - B3) LEN_S); [unfold DEP_SS, B3; lia | unfold LEN_S; lia | | | exact chunk_zero_s];
    rewrite CH3_length; unfold DEP_SS, B3, LEN_S; lia.
Qed.

(* [comment removed for export] *)
Lemma CH3_bytes : Z.to_N (to_Z (PrimString.length CH3) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma byte_zero_gen : forall off, 0 <= off < 0x55c000 ->
  PrimString.get CH3 (of_Z (2 * off)) = 48%uint63 -> PrimString.get CH3 (of_Z (2 * off + 1)) = 48%uint63 ->
  segment_byte_at [CH3] (Z.to_N off) = Some (Z_to_bv 8 0).
Proof.
  intros off Ho G0 G1. cbn [segment_byte_at]. rewrite CH3_bytes.
  destruct (N.ltb_spec (Z.to_N off) 0x55c000%N) as [Hlt|Hge]; [|lia].
  unfold hex_byte_at.
  replace (Z.of_N (2 * Z.to_N off)) with (2 * off) by lia.
  replace (Z.of_N (2 * Z.to_N off + 1)) with (2 * off + 1) by lia.
  assert (Hc1 : Uint63.ltb (of_Z (2 * off + 1)) (PrimString.length CH3) = true).
  { apply Uint63.ltb_spec. rewrite of_Z_spec. pose proof CH3_length as L. rewrite L.
    assert (Hw : 2 * 0x55c000 < wB) by (vm_compute; reflexivity). rewrite Z.mod_small by lia. lia. }
  rewrite Hc1. cbn [orb]. rewrite G0, G1. vm_compute. reflexivity.
Qed.

Lemma find_seg3 : forall x, 0xa0000 <= x -> x + 1 <= 0x5fc000 -> find_segment SEGS x 1 = Some SEG3.
Proof.
  intros x H1 H2. unfold Asan.M.loaded_segments, Asan_loaded_segments.
  cbn [find_segment]. cbn [seg_base seg_size Asan_segment_000 Asan_segment_001
                          Asan_segment_002 Asan_segment_003].
  destruct (Z.leb (Z.of_N 0x10000) x && Z.leb (x + 1) (Z.of_N 0x10000 + Z.of_N 0x20000))%bool eqn:E0.
  { apply andb_prop in E0 as [_ E0]. apply Z.leb_le in E0. lia. }
  destruct (Z.leb (Z.of_N 0x30000) x && Z.leb (x + 1) (Z.of_N 0x30000 + Z.of_N 0x6e000))%bool eqn:E1.
  { apply andb_prop in E1 as [_ E1]. apply Z.leb_le in E1. lia. }
  destruct (Z.leb (Z.of_N 0x9e000) x && Z.leb (x + 1) (Z.of_N 0x9e000 + Z.of_N 0x2000))%bool eqn:E2.
  { apply andb_prop in E2 as [_ E2]. apply Z.leb_le in E2. lia. }
  replace (Z.leb (Z.of_N 0xa0000) x && Z.leb (x + 1) (Z.of_N 0xa0000 + Z.of_N 0x55c000))%bool with true
    by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma SEG3_rw : seg_writable SEG3 = true /\ seg_readable SEG3 = true.
Proof. split; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Definition img_byte_ok (x : Z) : Prop :=
  exists seg b, find_segment SEGS x 1 = Some seg /\ seg_writable seg = true /\ seg_readable seg = true
    /\ segment_byte_at (seg_bytes seg) (Z.to_N (x - Z.of_N (seg_base seg))) = Some b /\ bv_unsigned b = 0.

Lemma img_byte_ok_d : forall x, DEP_D <= x < DEP_D + LEN_D -> img_byte_ok x.
Proof.
  intros x Hx. unfold DEP_D, LEN_D in Hx. exists SEG3, (Z_to_bv 8 0).
  split; [apply find_seg3; lia|]. split; [exact (proj1 SEG3_rw)|]. split; [exact (proj2 SEG3_rw)|].
  split; [|reflexivity].
  change (seg_bytes SEG3) with [CH3]. change (seg_base SEG3) with 0xa0000%N. change (Z.of_N 0xa0000%N) with 0xa0000.
  apply byte_zero_gen; [lia | apply get_zero_d; unfold DEP_D, B3, LEN_D; lia | apply get_zero_d; unfold DEP_D, B3, LEN_D; lia].
Qed.

Lemma img_byte_ok_s : forall x, DEP_SS <= x < DEP_SS + LEN_S -> img_byte_ok x.
Proof.
  intros x Hx. unfold DEP_SS, LEN_S in Hx. exists SEG3, (Z_to_bv 8 0).
  split; [apply find_seg3; lia|]. split; [exact (proj1 SEG3_rw)|]. split; [exact (proj2 SEG3_rw)|].
  split; [|reflexivity].
  change (seg_bytes SEG3) with [CH3]. change (seg_base SEG3) with 0xa0000%N. change (Z.of_N 0xa0000%N) with 0xa0000.
  apply byte_zero_gen; [lia | apply get_zero_s; unfold DEP_SS, B3, LEN_S; lia | apply get_zero_s; unfold DEP_SS, B3, LEN_S; lia].
Qed.

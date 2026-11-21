(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (scanN_sound, segment_byte_at_some1, scan63_sound and 11 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanHexScan () := "C56Stdlib6NArith6BinNat1N2ltK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02C56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N6eqb_eqC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00c59OSSVerify5KrLib2AS;AsanHexScan7byte_okC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4div2c59OSSVerify5KrLib2AS;AsanHexScan5scanNC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3addC56Stdlib6NArith6BinNat1N3subC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic3notC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib7Numbers7BinNums1Z02C46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;hex_byte_atK47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N7add_0_rC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C56Stdlib6NArith6BinNat1N3divC56Stdlib6NArith6BinNat1N8div2_divC56Stdlib6NArith6BinNat1N;lt_ge_casesC56Stdlib6NArith6BinNat1N2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat3N2Z6inj_ltK47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat3N2Z;inj_sub_maxC56Stdlib6ZArith4Znat3N2Z7inj_divC56Stdlib6ZArith4Znat3N2Z6inj_leC56Stdlib6ZArith4Znat3N2Z7inj_addC47Corelib7Strings:PrimString6stringI47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z4to_NC56Stdlib6NArith6BinNat1N3ltbC56Stdlib6NArith6BinNat1N6ltb_ltC46Stdlib9micromega;ZifyClasses3injC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib2AS;AsanHexScan;scanN_soundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC47Corelib7Strings:PrimString6lengthC67Corelib7Numbers6Cyclic5Int63<Uint63Axioms4to_ZC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib9micromega8ZifyInst7Inj_N_ZI47Corelib7Numbers7BinNums8positive00c59OSSVerify5KrLib2AS;AsanHexScan6scan63C1?~~~~~~~~~~~~~~~C47Corelib7Strings:PrimString3getC67Corelib7Numbers6Cyclic5Int639PrimInt633eqbC66Stdlib7Numbers6Cyclic5Int636Uint638eqb_specC67Corelib7Numbers6Cyclic5Int639PrimInt633lsrC67Corelib7Numbers6Cyclic5Int639PrimInt633addC67Corelib7Numbers6Cyclic5Int639PrimInt633subC66Stdlib7Numbers6Cyclic5Int636Uint638to_Z_injC66Stdlib7Numbers6Cyclic5Int636Uint63<to_Z_boundedC57Corelib7BinNums6IntDef1Z3powC57Corelib7BinNums6IntDef1Z3divC67Corelib7Numbers6Cyclic5Int63<Uint63Axioms8lsr_specC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01C57Corelib7BinNums6IntDef1Z3addC57Corelib7BinNums6IntDef1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC67Corelib7Numbers6Cyclic5Int63<Uint63Axioms8add_specC57Corelib7BinNums6IntDef1Z3subC67Corelib7Numbers6Cyclic5Int63<Uint63Axioms8sub_specC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC67Corelib7Numbers6Cyclic5Int63<Uint63Axioms2wBC67Corelib7Numbers6Cyclic5Int639PrimInt633intC66Stdlib7Numbers6Cyclic5Int636Uint636to_Z_0C47Corelib7Strings:PrimString6char63C66Stdlib7Numbers6Cyclic5Int636Uint636to_Z_1c59OSSVerify5KrLib2AS;AsanHexScan6hx_okcC1?~~~~~~~~~~~~~~~C67Corelib7Numbers6Cyclic5Int639PrimInt633lebC47Corelib4Init9Datatypes3orbC57Corelib7BinNums6IntDef1Z2leC67Corelib7Numbers6Cyclic5Int63<Uint63Axioms8leb_specC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:hex_nybbleC56Stdlib6NArith6BinNat1N3mulC67Corelib7Numbers6Cyclic5Int639PrimInt633ltbC57Corelib7BinNums6IntDef1Z2ltC67Corelib7Numbers6Cyclic5Int63<Uint63Axioms8ltb_specC45stdpp9bitvector;definitions7Z_to_bvc59OSSVerify5KrLib2AS;AsanHexScan=hx_okc_nybbleC1?~~~~~~~~~~~~~~~C67Corelib7Numbers6Cyclic5Int63<Uint63Axioms4of_Zc59OSSVerify5KrLib2AS;AsanHexScan6hx_okzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanHexScan<scan63_guardC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc59OSSVerify5KrLib2AS;AsanHexScanBscan63_guard_soundC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega:ZMicromega;ZArithProof03C66Stdlib7Numbers6Cyclic5Int636Uint639of_Z_specc59OSSVerify5KrLib2AS;AsanHexScan<scan63_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z7inj_mulc59OSSVerify5KrLib2AS;AsanHexScan9hexscan63C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanHexScan<scan63_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanHexScan>hex_byte_at_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanHexScan7zscan63C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanHexScan@hex_byte_at_zeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanHexScan9zrange_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib2AS;AsanHexScan8hexscanZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanHexScan?zrange_ok_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanHexScan?hexscan63_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanHexScan6zscanZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanHexScan=zscan63_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith4Znat3Z2N2idc59OSSVerify5KrLib2AS;AsanHexScan>hexscanZ_soundC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.

Definition byte_ok (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some _ => true | None => false end.

(* [comment removed for export] *)
Fixpoint scanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_ok s base
      else let h := N.div2 n in (scanN s f base h && scanN s f (base + h) (n - h))%bool
  end.

Lemma scanN_sound : forall s fuel base n,
  scanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N <> None.
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [scanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_ok in H.
      destruct (hex_byte_at s base); [discriminate|discriminate].
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)
Lemma segment_byte_at_some1 : forall s (n : N) (off : N),
  scanN s 64 0 n = true ->
  (n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N ->
  (Z.of_N off < Z.of_N n)%Z ->
  segment_byte_at [s] off <> None.
Proof.
  intros s n off Hs Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true
    by (symmetry; apply N.ltb_lt; lia).
  exact (scanN_sound s 64 0 n Hs off ltac:(lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import Uint63.

Definition hx_okc (c : PrimString.char63) : bool := ((48 <=? c)%uint63 && (c <=? 57)%uint63 || (97 <=? c)%uint63 && (c <=? 102)%uint63)%bool.
Definition hx_okz (c : PrimString.char63) : bool := (c =? 48)%uint63.

(* [comment removed for export] *)
Fixpoint scan63 (P : PrimString.char63 -> bool) (s : PrimString.string) (fuel : nat) (lo len : int) : bool :=
  match fuel with
  | O => (len =? 0)%uint63
  | S f =>
      if (len =? 0)%uint63 then true
      else if (len =? 1)%uint63 then P (PrimString.get s lo)
      else let h := (len >> 1)%uint63 in (scan63 P s f lo h && scan63 P s f (lo + h)%uint63 (len - h)%uint63)%bool
  end.

Lemma scan63_sound : forall P s fuel lo len,
  scan63 P s fuel lo len = true -> (to_Z lo + to_Z len < wB)%Z ->
  forall j, (to_Z lo <= to_Z j < to_Z lo + to_Z len)%Z -> P (PrimString.get s j) = true.
Proof.
  intros P s fuel. induction fuel as [|f IH]; intros lo len H Hov j Hj; cbn [scan63] in H.
  - apply eqb_spec in H. subst len. rewrite to_Z_0 in Hj. lia.
  - destruct (len =? 0)%uint63 eqn:E0. { apply eqb_spec in E0. subst len. rewrite to_Z_0 in Hj. lia. }
    destruct (len =? 1)%uint63 eqn:E1.
    { apply eqb_spec in E1. subst len. rewrite to_Z_1 in Hj. assert (j = lo) by (apply to_Z_inj; lia). subst j. exact H. }
    apply andb_prop in H as [H1 H2].
    pose proof (to_Z_bounded len) as Bl. pose proof (to_Z_bounded lo) as Bo.
    assert (Hh : to_Z (len >> 1)%uint63 = (to_Z len / 2)%Z) by (rewrite lsr_spec, to_Z_1; reflexivity).
    assert (Hq : (0 <= to_Z len / 2 <= to_Z len)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (Hlh : to_Z (lo + (len >> 1))%uint63 = (to_Z lo + to_Z len / 2)%Z) by (rewrite add_spec, Hh; apply Z.mod_small; lia).
    assert (Hsub : to_Z (len - (len >> 1))%uint63 = (to_Z len - to_Z len / 2)%Z) by (rewrite sub_spec, Hh; apply Z.mod_small; lia).
    destruct (Z.lt_ge_cases (to_Z j) (to_Z lo + to_Z len / 2)) as [L|G].
    + apply (IH lo (len >> 1)%uint63 H1); [rewrite Hh; lia | rewrite Hh; lia].
    + apply (IH (lo + (len >> 1))%uint63 (len - (len >> 1))%uint63 H2); [rewrite Hlh, Hsub; lia | rewrite Hlh, Hsub; lia].
Qed.

Lemma hx_okc_nybble : forall c, hx_okc c = true -> N.ltb (hex_nybble c) 16 = true.
Proof.
  intros c H. unfold hx_okc in H. unfold hex_nybble.
  assert (T48 : to_Z 48 = 48%Z) by reflexivity. assert (T57 : to_Z 57 = 57%Z) by reflexivity.
  assert (T97 : to_Z 97 = 97%Z) by reflexivity. assert (T102 : to_Z 102 = 102%Z) by reflexivity.
  destruct ((48 <=? c)%uint63 && (c <=? 57)%uint63)%bool eqn:E1.
  - cbv iota. apply andb_prop in E1 as [A B]. apply leb_spec in A. apply leb_spec in B. rewrite T48 in A. rewrite T57 in B.
    apply N.ltb_lt. lia.
  - try rewrite E1 in H. cbn [orb] in H. rewrite H. cbv iota. apply andb_prop in H as [A B]. apply leb_spec in A. apply leb_spec in B.
    rewrite T97 in A. rewrite T102 in B. apply N.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma hex_byte_at_ok : forall s (i : N),
  (to_Z (Uint63.of_Z (Z.of_N (2 * i + 1))) < to_Z (PrimString.length s))%Z ->
  hx_okc (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i)))) = true ->
  hx_okc (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i + 1)))) = true ->
  hex_byte_at s i <> None.
Proof.
  intros s i Hlen H0 H1. unfold hex_byte_at. cbv zeta.
  replace (Uint63.of_Z (Z.of_N (2 * i + 1)) <? PrimString.length s)%uint63 with true by (symmetry; apply ltb_spec; exact Hlen).
  cbn [orb]. rewrite (hx_okc_nybble _ H0), (hx_okc_nybble _ H1). cbn [andb]. discriminate.
Qed.
Lemma hex_byte_at_zero : forall s (i : N),
  (to_Z (Uint63.of_Z (Z.of_N (2 * i + 1))) < to_Z (PrimString.length s))%Z ->
  hx_okz (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i)))) = true ->
  hx_okz (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i + 1)))) = true ->
  hex_byte_at s i = Some (Z_to_bv 8 0).
Proof.
  intros s i Hlen H0 H1. unfold hx_okz in H0, H1. apply eqb_spec in H0. apply eqb_spec in H1.
  unfold hex_byte_at. cbv zeta.
  replace (Uint63.of_Z (Z.of_N (2 * i + 1)) <? PrimString.length s)%uint63 with true by (symmetry; apply ltb_spec; exact Hlen).
  cbn [orb]. rewrite H0, H1. reflexivity.
Qed.

(* [comment removed for export] *)
Definition scan63_guard (s : PrimString.string) (b2 n2 : int) : bool :=
  ((b2 <=? 2305843009213693952)%uint63 && (n2 <=? 2305843009213693952)%uint63 && ((b2 + n2)%uint63 <=? PrimString.length s)%uint63)%bool.
Definition hexscan63 (s : PrimString.string) (b2 n2 : int) : bool := (scan63_guard s b2 n2 && scan63 hx_okc s 64 b2 n2)%bool.
Definition zscan63 (s : PrimString.string) (b2 n2 : int) : bool := (scan63_guard s b2 n2 && scan63 hx_okz s 64 b2 n2)%bool.

Lemma scan63_guard_sound : forall s b2 n2, scan63_guard s b2 n2 = true ->
  (to_Z b2 + to_Z n2 < wB /\ to_Z b2 + to_Z n2 <= to_Z (PrimString.length s))%Z.
Proof.
  intros s b2 n2 H. unfold scan63_guard in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply leb_spec in H1. apply leb_spec in H2. apply leb_spec in H3.
  assert (T : to_Z 2305843009213693952 = 2305843009213693952%Z) by reflexivity. rewrite T in H1, H2.
  pose proof (to_Z_bounded b2). pose proof (to_Z_bounded n2).
  assert (W : wB = 9223372036854775808%Z) by reflexivity.
  rewrite add_spec, Z.mod_small in H3 by lia. lia.
Qed.

Lemma scan63_bytes : forall P s b2 n2 (i : N),
  scan63_guard s b2 n2 = true -> scan63 P s 64 b2 n2 = true ->
  (to_Z b2 <= 2 * Z.of_N i)%Z -> (2 * Z.of_N i + 1 < to_Z b2 + to_Z n2)%Z ->
  (to_Z (Uint63.of_Z (Z.of_N (2 * i + 1))) < to_Z (PrimString.length s))%Z
  /\ P (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i)))) = true
  /\ P (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i + 1)))) = true.
Proof.
  intros P s b2 n2 i G S L U. destruct (scan63_guard_sound _ _ _ G) as [OV LEN].
  pose proof (to_Z_bounded b2). pose proof (to_Z_bounded n2).
  assert (E0 : to_Z (Uint63.of_Z (Z.of_N (2 * i))) = (2 * Z.of_N i)%Z) by (rewrite of_Z_spec, Z.mod_small by lia; lia).
  assert (E1 : to_Z (Uint63.of_Z (Z.of_N (2 * i + 1))) = (2 * Z.of_N i + 1)%Z) by (rewrite of_Z_spec, Z.mod_small by lia; lia).
  split; [rewrite E1; lia|]. split; apply (scan63_sound P s 64 b2 n2 S OV); [rewrite E0 | rewrite E1]; lia.
Qed.

Lemma hexscan63_sound : forall s b2 n2, hexscan63 s b2 n2 = true ->
  forall i : N, (to_Z b2 <= 2 * Z.of_N i)%Z -> (2 * Z.of_N i + 1 < to_Z b2 + to_Z n2)%Z -> hex_byte_at s i <> None.
Proof.
  intros s b2 n2 H i L U. unfold hexscan63 in H. apply andb_prop in H as [G S].
  destruct (scan63_bytes hx_okc s b2 n2 i G S L U) as (A & B & C). exact (hex_byte_at_ok s i A B C).
Qed.
Lemma zscan63_sound : forall s b2 n2, zscan63 s b2 n2 = true ->
  forall i : N, (to_Z b2 <= 2 * Z.of_N i)%Z -> (2 * Z.of_N i + 1 < to_Z b2 + to_Z n2)%Z -> hex_byte_at s i = Some (Z_to_bv 8 0).
Proof.
  intros s b2 n2 H i L U. unfold zscan63 in H. apply andb_prop in H as [G S].
  destruct (scan63_bytes hx_okz s b2 n2 i G S L U) as (A & B & C). exact (hex_byte_at_zero s i A B C).
Qed.

(* [comment removed for export] *)
Definition zrange_ok (b n : Z) : bool :=
  ((0 <=? b)%Z && (0 <=? n)%Z && (b <? 1152921504606846976)%Z && (n <? 1152921504606846976)%Z)%bool.   (* [comment removed for export] *)
Definition hexscanZ (s : PrimString.string) (b n : Z) : bool := (zrange_ok b n && hexscan63 s (of_Z (2 * b)) (of_Z (2 * n)))%bool.
Definition zscanZ (s : PrimString.string) (b n : Z) : bool := (zrange_ok b n && zscan63 s (of_Z (2 * b)) (of_Z (2 * n)))%bool.

Lemma zrange_ok_sound : forall b n, zrange_ok b n = true ->
  (to_Z (of_Z (2 * b)) = 2 * b /\ to_Z (of_Z (2 * n)) = 2 * n /\ 0 <= b /\ 0 <= n)%Z.
Proof.
  intros b n H. unfold zrange_ok in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.ltb_lt in H4.
  assert (W : wB = 9223372036854775808%Z) by reflexivity.
  rewrite !of_Z_spec, !Z.mod_small by lia. lia.
Qed.

Lemma hexscanZ_sound : forall s b n, hexscanZ s b n = true ->
  forall i : N, (b <= Z.of_N i < b + n)%Z -> hex_byte_at s i <> None.
Proof.
  intros s b n H i Hi. unfold hexscanZ in H. apply andb_prop in H as [R H]. destruct (zrange_ok_sound _ _ R) as (E1 & E2 & _ & _).
  apply (hexscan63_sound _ _ _ H i); rewrite ?E1, ?E2; lia.
Qed.
Lemma zscanZ_sound : forall s b n, zscanZ s b n = true ->
  forall i : N, (b <= Z.of_N i < b + n)%Z -> hex_byte_at s i = Some (Z_to_bv 8 0).
Proof.
  intros s b n H i Hi. unfold zscanZ in H. apply andb_prop in H as [R H]. destruct (zrange_ok_sound _ _ R) as (E1 & E2 & _ & _).
  apply (zscan63_sound _ _ _ H i); rewrite ?E1, ?E2; lia.
Qed.

(* [comment removed for export] *)
Lemma segment_byte_at_someZ : forall s (n : Z) (off : N),
  hexscanZ s 0 n = true -> (Z.of_N off < n)%Z -> segment_byte_at [s] off <> None.
Proof.
  intros s n off H Hoff. cbn [segment_byte_at].
  pose proof H as H'. unfold hexscanZ in H'. apply andb_prop in H' as [R H'']. destruct (zrange_ok_sound _ _ R) as (E1 & E2 & _ & _).
  unfold hexscan63 in H''. apply andb_prop in H'' as [G _]. destruct (scan63_guard_sound _ _ _ G) as [_ LEN].
  rewrite E1, E2 in LEN. pose proof (to_Z_bounded (PrimString.length s)).
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true.
  - apply (hexscanZ_sound s 0 n H off). lia.
  - symmetry. apply N.ltb_lt. apply N2Z.inj_lt. rewrite Z2N.id by (apply Z.div_pos; lia).
    assert (Z.of_N off + 1 <= to_Z (PrimString.length s) / 2)%Z by (apply Z.div_le_lower_bound; lia). lia.
Qed.

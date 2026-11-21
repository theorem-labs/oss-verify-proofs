(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (11 recorded proofs replaced by written proofs (forallb_In, iota_Z_In, existsb_false_forall and 8 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec CatExec SeqExec StepTac MemSplit.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ZStores () := "C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib2AS7ZStores6iota_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2or01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C46Stdlib5Lists4List7existsbC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool=orb_false_iffK47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic2ex00C46Stdlib4Bool4Bool<orb_true_iffK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List=repeat_lengthC46Stdlib5Lists4List:nth_repeatc59OSSVerify5KrLib2AS7ZStores5zerosC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib2AS7ZStores9nth_zerosC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes6lengthc59OSSVerify5KrLib2AS7ZStores<length_zerosC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib2AS8MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8MemSplit9rdn_constC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3lorC47Corelib5Lists7ListDef6repeatI47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib2AS7ZStores6ws_inbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7ZStores:covers_offC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7ZStores7zstoresC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6leb_gtK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib2AS8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula06c59OSSVerify5KrLib2AS7ZStoresCexistsb_true_existsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib2AS7ZStoresDexistsb_false_forallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7ZStores<zstores_missC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7ZStores8ws_coverC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decc59OSSVerify5KrLib2AS7ZStores:forallb_InC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib2AS7ZStores9iota_Z_InC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7ZStores;zstores_hitC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionality".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Fixpoint zstores (m : word -> option byte) (d : word) (ws : list (Z * nat)) : word -> option byte :=
  match ws with
  | [] => m
  | (o, n) :: ws' => zstores (wbytes m (Z_to_bv 64 (bv_unsigned d + o)) (zeros n)) d ws'
  end.

Definition covers_off (i : Z) (on : Z * nat) : bool :=
  (fst on <=? i) && (i <? fst on + Z.of_nat (snd on)).

Definition ws_inb (ws : list (Z * nat)) (N : Z) : bool :=
  forallb (fun on => (0 <=? fst on) && (fst on + Z.of_nat (snd on) <=? N)) ws.

Fixpoint iota_Z (i : Z) (k : nat) : list Z :=
  match k with O => [] | S k' => i :: iota_Z (i + 1) k' end.

Definition ws_cover (ws : list (Z * nat)) (N : nat) : bool :=
  forallb (fun i => existsb (covers_off i) ws) (iota_Z 0 N).

Lemma forallb_In : forall {A} (f : A -> bool) l x, forallb f l = true -> In x l -> f x = true.
Proof.
  induction l as [|y l IH]; intros x H Hin; [contradiction|].
  cbn in H. apply andb_true_iff in H as [Hy Hl].
  destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma iota_Z_In : forall k i z, i <= z < i + Z.of_nat k -> In z (iota_Z i k).
Proof.
  induction k as [|k IH]; intros i z Hz; [lia|].
  cbn. destruct (Z.eq_dec i z); [left; assumption | right]. apply IH. lia.
Qed.

Lemma existsb_false_forall : forall {A} (f : A -> bool) l,
  existsb f l = false -> forall x, In x l -> f x = false.
Proof.
  induction l as [|y l IH]; intros H x Hin; [contradiction|].
  cbn in H. apply orb_false_iff in H as [Hy Hl].
  destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma existsb_true_exists : forall {A} (f : A -> bool) l,
  existsb f l = true -> exists x, In x l /\ f x = true.
Proof.
  induction l as [|y l IH]; intros H; [discriminate|].
  cbn in H. apply orb_true_iff in H as [Hy|Hl].
  - exists y. split; [left; reflexivity | exact Hy].
  - destruct (IH Hl) as [x [Hin Hx]]. exists x. split; [right; exact Hin | exact Hx].
Qed.

Lemma length_zeros : forall n, length (zeros n) = n.
Proof. intro n. apply repeat_length. Qed.

Lemma nth_zeros : forall n k, nth k (zeros n) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. intros n k. unfold zeros. apply nth_repeat. Qed.

Lemma rdn_wbytes_zeros_in : forall segs m (d a : word) (N n : nat),
  bv_unsigned d + Z.of_nat N < 2^64 ->
  bv_unsigned d <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned d + Z.of_nat N ->
  rdn segs (wbytes m d (zeros N)) a n = Some (zeros n).
Proof.
  intros segs m d a N n Hnw Hlo Hhi. unfold zeros at 2. apply rdn_const; [lia|].
  intros x Hx. rewrite wbytes_inside by (rewrite length_zeros; lia).
  f_equal. apply nth_zeros.
Qed.

Lemma bytes_le_to_Z_zeros : forall n, bytes_le_to_Z (zeros n) = 0.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [zeros repeat bytes_le_to_Z].
  fold (zeros n). rewrite IH. reflexivity.
Qed.

Section Cover.
  Variable d : word.
  Variable N : Z.
  Hypothesis Hnw : bv_unsigned d + N < 2^64.

  Lemma zstores_miss : forall ws m (x : word),
    ws_inb ws N = true ->
    (forall on, In on ws -> covers_off (bv_unsigned x - bv_unsigned d) on = false) ->
    zstores m d ws x = m x.
  Proof.
    induction ws as [|[o n] ws IH]; intros m x Hinb Hno; [reflexivity|].
    cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
    apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
    apply Z.leb_le in Ho. apply Z.leb_le in Hn.
    rewrite IH; [| exact Hinb | intros on Hin; apply Hno; right; exact Hin].
    pose proof (Hno (o, n) (or_introl eq_refl)) as Hc. cbn [covers_off fst snd] in Hc.
    pose proof (u64_range x). pose proof (u64_range d).
    apply wbytes_outside.
    - rewrite length_zeros. rewrite u_Z2bv by lia. lia.
    - rewrite length_zeros. rewrite u_Z2bv by lia.
      apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc];
        cbn [fst snd] in Hc; lia.
  Qed.

  Lemma zstores_hit : forall ws m (x : word),
    ws_inb ws N = true ->
    (exists on, In on ws /\ covers_off (bv_unsigned x - bv_unsigned d) on = true) ->
    zstores m d ws x = Some (Z_to_bv 8 0).
  Proof.
    induction ws as [|[o n] ws IH]; intros m x Hinb Hex.
    { destruct Hex as [on [[] _]]. }
    cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
    apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
    apply Z.leb_le in Ho. apply Z.leb_le in Hn.
    destruct (existsb (covers_off (bv_unsigned x - bv_unsigned d)) ws) eqn:E.
    - apply IH; [exact Hinb|]. apply existsb_true_exists. exact E.
    - rewrite zstores_miss; [| exact Hinb | apply existsb_false_forall; exact E].
      destruct Hex as [on [[<-|Hin] Hc]].
      2:{ rewrite (existsb_false_forall _ _ E on Hin) in Hc. discriminate. }
      cbn [covers_off fst snd] in Hc. apply andb_true_iff in Hc as [Hc1 Hc2].
      apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2. cbn [fst snd] in Hc1, Hc2.
      pose proof (u64_range x). pose proof (u64_range d).
      rewrite wbytes_inside by (rewrite length_zeros, u_Z2bv by lia; lia).
      f_equal. apply nth_zeros.
  Qed.

  Lemma zstores_cover : forall ws m (n : nat),
    Z.of_nat n = N ->
    ws_inb ws N = true ->
    ws_cover ws n = true ->
    zstores m d ws = wbytes m d (zeros n).
  Proof.
    intros ws m n HnN Hinb Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range x). pose proof (u64_range d).
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d)) as [Hlt|Hge].
    { rewrite wbytes_outside by (rewrite length_zeros; lia).
      apply zstores_miss; [exact Hinb|]. intros [o k] Hin.
      pose proof (forallb_In _ _ _ Hinb Hin) as Hb. cbn [fst snd] in Hb.
      apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1.
      cbn [covers_off fst snd]. apply andb_false_iff. left. apply Z.leb_gt. cbn [fst snd]. lia. }
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d + N)) as [Hin|Hout].
    - rewrite wbytes_inside by (rewrite length_zeros; lia). rewrite nth_zeros.
      apply zstores_hit; [exact Hinb|].
      pose proof (forallb_In _ _ _ Hcov (iota_Z_In n 0 (bv_unsigned x - bv_unsigned d) ltac:(lia))) as He.
      apply existsb_true_exists in He. exact He.
    - rewrite wbytes_outside by (rewrite length_zeros; lia).
      apply zstores_miss; [exact Hinb|]. intros [o k] Hin'.
      pose proof (forallb_In _ _ _ Hinb Hin') as Hb. cbn [fst snd] in Hb.
      apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb2.
      cbn [covers_off fst snd]. apply andb_false_iff. right. apply Z.ltb_ge. cbn [fst snd]. lia.
  Qed.
End Cover.

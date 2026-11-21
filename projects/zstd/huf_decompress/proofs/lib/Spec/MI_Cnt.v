(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (18 recorded proofs replaced by written proofs (in_zrange, forallb_zrange, size_class_lt and 15 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Malloc MI_Arith.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Cnt () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List2InI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic3iffC46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z2ltC47Corelib5Lists7ListDef3seqI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib4Spec6MI_Cnt6zrangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C47Corelib7Classes?RelationClasses>iff_TransitiveK47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib5Lists4List7forallbC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallc59OSSVerify5KrLib4Spec6MI_Cnt9in_zrangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02c59OSSVerify5KrLib4Spec6MI_Cnt6mono_fC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Cnt>forallb_zrangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool<orb_true_iffC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec6MI_Cnt;mono_b_trueC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib4Spec6MI_Cnt=size_class_ltC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z;lt_ge_casesc59OSSVerify5KrLib4Spec6MI_Cnt=size_class_leC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrc59OSSVerify5KrLib4Spec6MI_Cnt5stc_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Cnt5stc_fC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Cnt?size_to_class_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00c59OSSVerify5KrLib4Spec6MI_Cnt=stc_ok_b_trueC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4evenC56Stdlib6ZArith6BinInt1Z4EvenC56Stdlib6ZArith6BinInt1Z9even_specC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z3oddC56Stdlib6ZArith6BinInt1Z4succC46Stdlib4Bool4Bool:orb_true_rC56Stdlib6ZArith6BinInt1Z8odd_succC56Stdlib6ZArith6BinInt1Z8bit0_oddC56Stdlib6ZArith6BinInt1Z;testbit_0_lC56Stdlib6ZArith6BinInt1Z@testbit_odd_succC46Stdlib4Bool4Bool;orb_false_rC56Stdlib6ZArith6BinInt1ZAtestbit_even_succC56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C59OSSVerify5KrLib4Spec6Malloc:halve_evenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Cnt7he_listC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes7nat_indC59OSSVerify5KrLib4Spec6Malloc>small_cnt_pickC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc7med_cntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9small_cntC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Cnt=halve_even_inC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapc59OSSVerify5KrLib4Spec6MI_Cnt7cnt0_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Cnt9cnt0_listC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Cnt;ag_check_scC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundc59OSSVerify5KrLib4Spec6MI_Cnt6grp_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02c59OSSVerify5KrLib4Spec6MI_Cnt7nest_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z:ones_equivC59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Cnt@round_up_pg_specC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Cnt4bumpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Cnt7cnt0_inC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib4Spec6MI_Cnt4qmaxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Cnt3adjC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_CntAround_up_pg_pagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Arith@size_class_boundC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib4Spec6MI_Cnt=ag_check_trueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z8leb_specC59OSSVerify5KrLib4Spec8MI_ArithAtestbit_mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1ZAsub_nocarry_ldiffC59OSSVerify5KrLib4Spec8MI_Arith@mask_upto_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z<ldiff_nonnegC56Stdlib6ZArith6BinInt1Z7compareC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool<andb_false_rI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03K47Corelib4Init5Logic4True01".
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition zrange (lo n : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat n)).
Lemma in_zrange lo n x : 0 <= n -> (In x (zrange lo n) <-> lo <= x < lo + n).
Proof.
  intros Hn. unfold zrange. rewrite in_map_iff. split.
  - intros (i & <- & Hi). apply in_seq in Hi. lia.
  - intros H. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma forallb_zrange f lo n x : forallb f (zrange lo n) = true -> 0 <= n -> lo <= x < lo + n -> f x = true.
Proof. intros H Hn Hx. rewrite forallb_forall in H. apply H. apply in_zrange; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mono_f (a : Z) : bool := forallb (fun b => negb (a <? b) || (size_class a <? size_class b)) (zrange 0 48).
Lemma mono_b_true : forallb mono_f (zrange 0 48) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Cnt ()) [] "p;2p;1p;3g0099j26Tg00A]j15Tg00@Uj10Tg00e4j11Tg00Lmj24Tg00bJj32Tg00E8j33Tg00`fR0g00aFR1'6g00VSg00eRg00UVg00`A#5#0#0#0#0#1'432=301do"). Qed.

Lemma size_class_lt a b : 0 <= a < 48 -> 0 <= b < 48 -> a < b -> size_class a < size_class b.
Proof.
  intros Ha Hb Hab. pose proof (forallb_zrange mono_f 0 48 a mono_b_true ltac:(lia) ltac:(lia)) as H. unfold mono_f in H.
  pose proof (forallb_zrange _ 0 48 b H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
  apply orb_true_iff in H2. destruct H2 as [H2|H2]; [apply negb_true_iff in H2; apply Z.ltb_ge in H2; lia| apply Z.ltb_lt in H2; exact H2].
Qed.
Lemma size_class_le a b : 0 <= a < 48 -> 0 <= b < 48 -> a <= b -> size_class a <= size_class b.
Proof. intros. destruct (Z.eq_dec a b) as [->|]; [lia|]. pose proof (size_class_lt a b). lia. Qed.
Lemma size_class_lt_inv a b : 0 <= a < 48 -> 0 <= b < 48 -> size_class a < size_class b -> a < b.
Proof. intros. destruct (Z.lt_ge_cases a b); [assumption|]. pose proof (size_class_le b a). lia. Qed.

(* [comment removed for export] *)
Definition stc_k (k : Z) : Z :=
  if k <? 10 then k else
  let n := k + 1 in
  let i := (28 - clz32 n) * 4 + 8 in
  let i := if size_class (i + 1) <? n then i + 2 else i in
  if size_class i <? n then i + 1 else i.
Lemma size_to_class_k n : size_to_class n = stc_k (Z.shiftr (n + IB - 1) 4).
Proof. reflexivity. Qed.

Definition stc_f (k : Z) : bool := let sc := stc_k k in (0 <=? sc) && (sc <? 48) && (k + 1 <=? size_class sc).
Lemma stc_ok_b_true : forallb stc_f (zrange 0 8191) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Cnt ()) [] "p;2p;1p;3g0099j26Tg00e4j13Tg00Lmj22Tg00bJj35Tg00E8j34Tg00A]j11Tf0#1#1p=0g00`fR0g00aFR1'6g00VSg014Zg00UVg00`A#0#0#0#0#0#0#3'235=401do"). Qed.

Lemma size_to_class_ok n : 0 <= n < MMAP_THRESHOLD ->
  0 <= size_to_class n < 48 /\ n + IB <= UNIT * size_class (size_to_class n).
Proof.
  intros Hn. rewrite size_to_class_k. rewrite Z.shiftr_div_pow2 by lia. unfold IB, UNIT, MMAP_THRESHOLD in *.
  set (k := (n + 4 - 1) / 2 ^ 4).
  assert (Hk : 0 <= k < 8191) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (Hk2 : 16 * k <= n + 3 < 16 * k + 16) by (subst k; change (2 ^ 4) with 16; pose proof (Z.div_mod (n + 4 - 1) 16 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 4 - 1) 16 ltac:(lia)); lia).
  pose proof (forallb_zrange stc_f 0 8191 k stc_ok_b_true ltac:(lia) ltac:(lia)) as H. unfold stc_f in H. cbn zeta in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. lia.
Qed.

(* [comment removed for export] *)
Lemma lor1_even sc : 0 <= sc -> Z.even sc = true -> Z.lor sc 1 = sc + 1.
Proof.
  intros H He. assert (HE : Z.Even sc) by (apply Z.even_spec; exact He). destruct HE as [m ->].
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite !Z.bit0_odd. replace (2 * m + 1) with (Z.succ (2 * m)) by lia. rewrite Z.odd_succ, He. change (Z.odd 1) with true. apply orb_true_r.
  - assert (T1 : forall k, 0 <= k -> Z.testbit 1 (Z.succ k) = false).
    { intros k Hk. change (Z.testbit 1) with (Z.testbit (2 * 0 + 1)). rewrite Z.testbit_odd_succ by exact Hk. apply Z.testbit_0_l. }
    replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ, Z.testbit_odd_succ, T1 by lia.
    apply orb_false_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint he_list (f : nat) (c : Z) : list Z :=
  match f with
  | O => [c]
  | S f' => c :: (if Z.even c then he_list f' (Z.shiftr c 1) else [])
  end.
Lemma halve_even_in f : forall c u, In (halve_even f c u) (he_list f c).
Proof.
  induction f as [|f IH]; intros c u; cbn [halve_even he_list]; [left; reflexivity|].
  destruct (Z.even c); cbn [andb]; [| left; reflexivity].
  destruct (u <? 4 * c); [right; apply IH| left; reflexivity].
Qed.

Definition cnt0_list (sc : Z) : list Z :=
  let size := UNIT * size_class sc in
  if sc <? 9 then [small_cnt sc 0; small_cnt sc 1; small_cnt sc 2]
  else map (fun c => halve_big 8 c size) (he_list 8 (med_cnt (Z.land sc 3))).

Definition cnt0_of (sc u : Z) : Z :=
  if sc <? 9 then small_cnt_pick sc u
  else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) (UNIT * size_class sc).

Lemma cnt0_in sc u : In (cnt0_of sc u) (cnt0_list sc).
Proof.
  unfold cnt0_of, cnt0_list. destruct (sc <? 9).
  - unfold small_cnt_pick. destruct (negb (u <? 4 * small_cnt sc 0)); [left; reflexivity|].
    destruct (negb (u <? 4 * small_cnt sc 1)); [right; left; reflexivity| right; right; left; reflexivity].
  - apply (in_map (fun c => halve_big 8 c (UNIT * size_class sc))). apply halve_even_in.
Qed.

Definition bump (size c : Z) : Z := if (c =? 1) && (size * c + UNIT <=? PGSZ / 2) then 2 else c.

(* [comment removed for export] *)
Definition adj (sc size cnt : Z) : Z :=
  if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
  else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
  else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
  else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
  else cnt.

(* [comment removed for export] *)
Definition grp_ok (sc cnt needed : Z) : bool :=
  let size := UNIT * size_class sc in
  let maplen := Z.shiftr needed 12 in
  let last := cnt - 1 in
  let stride := if (last =? 0) && negb (maplen =? 0) then maplen * 4096 - UNIT else size in
  (1 <=? cnt) && (cnt <=? 32) && (needed mod 4096 =? 0) && (4096 <=? needed) && (needed <=? 2 ^ 20)
  && (UNIT + stride * cnt <=? maplen * 4096)
  && ((stride <=? size) || (28 <=? sc))
  && (negb (last =? 0) || (27 <=? sc))
  && (stride * cnt <? 2 ^ 20) && (16 <=? stride) && (stride mod 16 =? 0).

(* [comment removed for export] *)
Definition nest_ok (sc cnt : Z) : bool :=
  let size := UNIT * size_class sc in
  let n' := UNIT + cnt * size - IB in
  let j := size_to_class n' in
  (2 <=? cnt) && (cnt <=? 32) && (sc <? j) && (j <=? 23) && (UNIT + cnt * size <=? UNIT * size_class j) && (size * cnt <? 2 ^ 20)
  && (0 <=? n') && (n' + IB <=? 2048).

Definition qmax (sc : Z) : Z := (UNIT * size_class sc + UNIT + 4095) / 4096.

Definition ag_check_sc (sc : Z) : bool :=
  let size := UNIT * size_class sc in
  forallb (fun cnt0 =>
    let cnt1 := bump size cnt0 in
    if PGSZ / 2 <? size * cnt1 + UNIT then
      forallb (fun cnt2 =>
         grp_ok sc cnt2 (round_up_pg (size * cnt2 + UNIT))
         && (negb (cnt2 <=? 7)
             || forallb (fun q => negb ((q * 4096 <? size + UNIT) || (4 <=? q)) || (grp_ok sc 1 (q * 4096) && (28 <=? sc))) (zrange 1 (qmax sc))))
        [cnt1; adj sc size cnt1]
    else nest_ok sc cnt1)
  (cnt0_list sc).

Lemma ag_check_true : forallb ag_check_sc (zrange 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma grp_ok_sound sc cnt needed : grp_ok sc cnt needed = true ->
  let size := UNIT * size_class sc in
  let maplen := Z.shiftr needed 12 in
  let last := cnt - 1 in
  let stride := if (last =? 0) && negb (maplen =? 0) then maplen * 4096 - UNIT else size in
  1 <= cnt <= 32 /\ needed mod 4096 = 0 /\ 4096 <= needed <= 2 ^ 20 /\ maplen = needed / 4096 /\ 1 <= maplen <= 256
  /\ UNIT + stride * cnt <= maplen * 4096 /\ (stride <= size \/ 28 <= sc) /\ (last = 0 -> 27 <= sc)
  /\ stride * cnt < 2 ^ 20 /\ 16 <= stride /\ stride mod 16 = 0.
Proof.
  unfold grp_ok. intros H. cbn zeta. rewrite Z.shiftr_div_pow2 in * by lia. change (2 ^ 12) with 4096 in *.
  repeat (apply andb_true_iff in H as [H ?]).
  repeat match goal with
  | K : (_ <=? _) = true |- _ => apply Z.leb_le in K
  | K : (_ <? _) = true |- _ => apply Z.ltb_lt in K
  | K : (_ =? _) = true |- _ => apply Z.eqb_eq in K
  | K : (_ || _) = true |- _ => apply orb_true_iff in K
  end.
  assert (1 <= needed / 4096 <= 256) by (split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]).
  repeat split; try assumption; lia.
Qed.

Lemma nest_ok_sound sc cnt : nest_ok sc cnt = true ->
  let size := UNIT * size_class sc in
  let n' := UNIT + cnt * size - IB in
  let j := size_to_class n' in
  2 <= cnt <= 32 /\ sc < j <= 23 /\ UNIT + cnt * size <= UNIT * size_class j /\ size * cnt < 2 ^ 20 /\ 0 <= n' /\ n' + IB <= 2048.
Proof.
  unfold nest_ok. intros H. cbn zeta.
  repeat (apply andb_true_iff in H as [H ?]).
  repeat match goal with
  | K : (_ <=? _) = true |- _ => apply Z.leb_le in K
  | K : (_ <? _) = true |- _ => apply Z.ltb_lt in K
  end. repeat split; assumption.
Qed.

Lemma round_up_pg_spec x : x <= round_up_pg x < x + 4096 /\ round_up_pg x mod 4096 = 0.
Proof.
  unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.pred (2 ^ 12)). rewrite <- Z.ones_equiv, Z.land_ones by lia.
  change (2 ^ 12) with 4096.
  pose proof (Z.mod_pos_bound (- x) 4096 ltac:(lia)) as B. pose proof (Z.div_mod (- x) 4096 ltac:(lia)) as D.
  split; [lia|]. replace (x + - x mod 4096) with ((- ((- x) / 4096)) * 4096) by lia. apply Z.mod_mul. lia.
Qed.

Lemma round_up_pg_pages x : 0 < x -> exists q, round_up_pg x = q * 4096 /\ 1 <= q /\ (q - 1) * 4096 < x <= q * 4096.
Proof.
  intros Hx. destruct (round_up_pg_spec x) as [A B].
  exists (round_up_pg x / 4096). pose proof (Z.div_mod (round_up_pg x) 4096 ltac:(lia)). rewrite B in H. nia.
Qed.

(* [comment removed for export] *)
Theorem alloc_group_arith sc req u0 u1 (nosmall : bool) :
  0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  let size := UNIT * size_class sc in
  let cnt0 := cnt0_of sc u0 in
  let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0 in
  (PGSZ / 2 < size * cnt1 + UNIT ->
     let cnt2 :=
       if (u1 <? 4 * cnt1) && negb nosmall then
         if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt1) then 2
         else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt1) then 3
         else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt1) then 3
         else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt1) then 5
         else cnt1
       else cnt1 in
     let needed := round_up_pg (size * cnt2 + UNIT) in
     let '(cnt3, needed3) :=
       if negb nosmall && (cnt2 <=? 7) then
         let req' := round_up_pg (req + IB + UNIT) in
         if (req' <? size + UNIT) || ((4 * PGSZ <=? req') && (u1 <? 2 * cnt2)) then (1, req') else (cnt2, needed)
       else (cnt2, needed) in
     grp_ok sc cnt3 needed3 = true
     /\ ((cnt3 = 1 /\ needed3 = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (cnt3 = cnt2 /\ needed3 = needed /\ size * cnt2 + UNIT <= needed)))
  /\ (size * cnt1 + UNIT <= PGSZ / 2 -> nest_ok sc cnt1 = true).
Proof.
  intros Hsc Hreq Hfit. cbn zeta.
  pose proof (forallb_zrange ag_check_sc 0 48 sc ag_check_true ltac:(lia) ltac:(lia)) as H. unfold ag_check_sc in H.
  rewrite forallb_forall in H. specialize (H _ (cnt0_in sc u0)). cbn beta in H. fold (bump (UNIT * size_class sc) (cnt0_of sc u0)) in H |- *.
  set (cnt1 := bump (UNIT * size_class sc) (cnt0_of sc u0)) in *. clearbody cnt1.
  split.
  - intros HB. rewrite (proj2 (Z.ltb_lt _ _) HB) in H. rewrite forallb_forall in H.
    set (cnt2 := if (u1 <? 4 * cnt1) && negb nosmall then _ else cnt1).
    assert (Hc2 : In cnt2 [cnt1; adj sc (UNIT * size_class sc) cnt1]).
    { subst cnt2. destruct ((u1 <? 4 * cnt1) && negb nosmall); [right; left; reflexivity| left; reflexivity]. }
    specialize (H _ Hc2). clearbody cnt2. apply andb_true_iff in H as [G1 G2].
    destruct (negb nosmall && (cnt2 <=? 7)) eqn:E7.
    + destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * cnt2))) eqn:ER.
      * apply andb_true_iff in E7 as [_ E7]. rewrite E7 in G2. cbn [negb orb] in G2. rewrite forallb_forall in G2.
        destruct (round_up_pg_pages (req + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as (q & Eq & Hq1 & Hq2). rewrite Eq in *.
        assert (Hq : In q (zrange 1 (qmax sc))).
        { apply in_zrange; [unfold qmax, UNIT; apply Z.div_pos; [pose proof (size_class_bound sc Hsc); lia| lia]|].
          split; [lia|]. unfold qmax. unfold IB, UNIT, PGSZ in *.
          assert (q <= (16 * size_class sc + 16 + 4095) / 4096) by (apply Z.div_le_lower_bound; lia). lia. }
        specialize (G2 _ Hq). cbn beta in G2.
        assert (EC : (q * 4096 <? UNIT * size_class sc + UNIT) || (4 <=? q) = true).
        { apply orb_true_iff in ER. apply orb_true_iff. destruct ER as [ER|ER]; [left; exact ER| right].
          apply andb_true_iff in ER as [ER _]. apply Z.leb_le in ER. apply Z.leb_le. unfold PGSZ in ER. lia. }
        rewrite EC in G2. cbn [negb orb] in G2. apply andb_true_iff in G2 as [G2 G28]. apply Z.leb_le in G28.
        split; [exact G2| left; split; [reflexivity| split; [reflexivity| exact G28]]].
      * split; [exact G1| right; split; [reflexivity| split; [reflexivity| apply (proj1 (round_up_pg_spec _))]]].
    + split; [exact G1| right; split; [reflexivity| split; [reflexivity| apply (proj1 (round_up_pg_spec _))]]].
  - intros HN. assert (E : (PGSZ / 2 <? UNIT * size_class sc * cnt1 + UNIT) = false) by (apply Z.ltb_ge; lia).
    rewrite E in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma clamp_ai size cnt : 1 <= cnt ->
  let ai := (4096 - UNIT) / size - 1 in
  let ai := if cnt - 1 <? ai then cnt - 1 else ai in
  let ai := if ai <? 0 then 0 else ai in
  0 <= ai <= cnt - 1.
Proof.
  intros Hc. cbn zeta. destruct (Z.ltb_spec (cnt - 1) ((4096 - UNIT) / size - 1)).
  - destruct (Z.ltb_spec (cnt - 1) 0); lia.
  - destruct (Z.ltb_spec ((4096 - UNIT) / size - 1) 0); lia.
Qed.

(* [comment removed for export] *)
Lemma created_masks ai last :
  0 <= ai <= last -> last <= 31 ->
  let avail := mask_upto ai in
  let freed := mask_upto last - avail in
  0 <= avail /\ 0 <= freed
  /\ (forall i, 0 <= i -> Z.testbit avail i = true -> i <= ai)
  /\ (forall i, 0 <= i -> Z.testbit freed i = true -> i <= last)
  /\ (forall i, 0 <= i -> Z.testbit avail i = true -> Z.testbit freed i = true -> False)
  /\ (forall i, ai < i <= last -> Z.testbit freed i = true)
  /\ (forall i, 0 <= i <= ai -> Z.testbit avail i = true)
  /\ freed = Z.ldiff (mask_upto last) (mask_upto ai).
Proof.
  intros Hai Hl. cbn zeta.
  assert (EF : mask_upto last - mask_upto ai = Z.ldiff (mask_upto last) (mask_upto ai)).
  { apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, !testbit_mask_upto by lia.
    destruct (Z.leb_spec i ai); destruct (Z.leb_spec i last); cbn; try reflexivity. lia. }
  rewrite EF. pose proof (mask_upto_nonneg ai ltac:(lia)). pose proof (mask_upto_nonneg last ltac:(lia)).
  split; [assumption|]. split; [apply Z.ldiff_nonneg; left; assumption|].
  split; [intros i Hi Hb; rewrite testbit_mask_upto in Hb by lia; apply Z.leb_le in Hb; exact Hb|].
  split; [intros i Hi Hb; rewrite Z.ldiff_spec, !testbit_mask_upto in Hb by lia; destruct (Z.leb_spec i last); [lia| discriminate]|].
  split; [intros i Hi Ha Hb; rewrite Z.ldiff_spec, Ha in Hb; rewrite andb_false_r in Hb; discriminate|].
  split; [intros i Hi; rewrite Z.ldiff_spec, !testbit_mask_upto by lia; destruct (Z.leb_spec i last); destruct (Z.leb_spec i ai); cbn; try reflexivity; lia|].
  split; [intros i Hi; rewrite testbit_mask_upto by lia; apply Z.leb_le; lia| reflexivity].
Qed.

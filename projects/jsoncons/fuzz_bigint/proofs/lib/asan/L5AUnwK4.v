(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface BigLinkBase
     AsanAcct L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5DivSpecsA L5DivInnerSpecsA L5UnwindSpecsA L5ADetailH L5AFrameK L5AUnwK L5AUnwK2 L5AUnwK3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AUK4.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5AUK. Import L5AUK2. Import L5AUK3.
Abbreviation RSEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition keep (P : Prop) : Prop := P.

(* [comment removed for export] *)
Ltac expand_arr_at H n b off :=
  lazymatch n with
  | O => idtac
  | Datatypes.S ?m =>
      (let X := fresh "FC" in pose proof (H m ltac:(clear; Lia.lia)) as X; cbn [nth] in X;
       let z := eval vm_compute in (off + 8 * Z.of_nat m) in
       lazymatch type of X with L5.u64_at ?sg ?M ?a ?v =>
         lazymatch z with
         | 0 => replace a with b in X by (clear; Lia.lia)
         | _ => replace a with (b + z) in X by (clear; Lia.lia)
         end
       end);
      expand_arr_at H m b off
  end.
Ltac gmemf :=
  lazymatch goal with
  | |- L5.u64_at ?sg ?M ?a ?v => match goal with H : L5.u64_at sg M a ?v' |- _ => first [exact H | replace v with v' by (clear; Lia.lia); exact H] end
  end.
Ltac fcell CI :=
  with_ci CI ltac:(fun L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac =>
    lazymatch goal with
    | |- L5.u64_at _ (mrestrict _ _) ?a ?v =>
        apply (L5AUK.cv_u64 L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI a v); [ cvis_tac XB | nlia | nlia | gmemf ]
    end).

(* [comment removed for export] *)
Lemma sh_div_defined M F vn v0 vq vr vh : L5DIA.sh_div M F vn v0 vq vr vh -> L5.defined M (F / 8 + SB) 64.
Proof.
  intros (Ha & Hb & Hc & Hd & He & Hf & Hg & Hh & Hi' & Hj & Hk & Hl & Hm & Hn) i Hi.
  destruct (Z_lt_dec i 4) as [LT0|GE0]; [apply (shrun_def M F 0 4 _ i Ha); clear - Hi LT0 ; lia|].
  destruct (Z_lt_dec i 8) as [LT1|GE1]; [apply (shrun_def M F 4 4 _ i Hb); clear - Hi LT1 GE0; lia|].
  destruct (Z_lt_dec i 12) as [LT2|GE2]; [apply (shrun_def M F 8 4 _ i Hc); clear - Hi LT2 GE1; lia|].
  destruct (Z_lt_dec i 16) as [LT3|GE3]; [apply (shrun_def M F 12 4 _ i Hd); clear - Hi LT3 GE2; lia|].
  destruct (Z_lt_dec i 20) as [LT4|GE4]; [apply (shrun_def M F 16 4 _ i He); clear - Hi LT4 GE3; lia|].
  destruct (Z_lt_dec i 24) as [LT5|GE5]; [apply (shrun_def M F 20 4 _ i Hf); clear - Hi LT5 GE4; lia|].
  destruct (Z_lt_dec i 28) as [LT6|GE6]; [apply (shrun_def M F 24 4 _ i Hg); clear - Hi LT6 GE5; lia|].
  destruct (Z_lt_dec i 32) as [LT7|GE7]; [apply (shrun_def M F 28 4 _ i Hh); clear - Hi LT7 GE6; lia|].
  destruct (Z_lt_dec i 36) as [LT8|GE8]; [apply (shrun_def M F 32 4 _ i Hi'); clear - Hi LT8 GE7; lia|].
  destruct (Z_lt_dec i 40) as [LT9|GE9]; [apply (shrun_def M F 36 4 _ i Hj); clear - Hi LT9 GE8; lia|].
  destruct (Z_lt_dec i 44) as [LT10|GE10]; [apply (shrun_def M F 40 4 _ i Hk); clear - Hi LT10 GE9; lia|].
  destruct (Z_lt_dec i 48) as [LT11|GE11]; [apply (shrun_def M F 44 4 _ i Hl); clear - Hi LT11 GE10; lia|].
  destruct (Z_lt_dec i 52) as [LT12|GE12]; [apply (shrun_def M F 48 4 _ i Hm); clear - Hi LT12 GE11; lia|].
  destruct (Z_lt_dec i 64) as [LT13|GE13]; [apply (shrun_def M F 52 12 _ i Hn); clear - Hi LT13 GE12; lia|].
  exfalso. clear - Hi GE13. lia.
Qed.
Lemma sh_op_defined M F : L5DIA.sh_op M F -> L5.defined M (F / 8 + SB) 16.
Proof.
  intros (Ha & Hb & Hc & Hd) i Hi.
  destruct (Z_lt_dec i 4) as [LT0|GE0]; [apply (shrun_def M F 0 4 _ i Ha); clear - Hi LT0 ; lia|].
  destruct (Z_lt_dec i 8) as [LT1|GE1]; [apply (shrun_def M F 4 4 _ i Hb); clear - Hi LT1 GE0; lia|].
  destruct (Z_lt_dec i 12) as [LT2|GE2]; [apply (shrun_def M F 8 4 _ i Hc); clear - Hi LT2 GE1; lia|].
  destruct (Z_lt_dec i 16) as [LT3|GE3]; [apply (shrun_def M F 12 4 _ i Hd); clear - Hi LT3 GE2; lia|].
  exfalso. clear - Hi GE3. lia.
Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

(* [comment removed for export] *)
Lemma cinv_pure M0 model0 A0 LB FF Sp Scr W (WIMG : forall r a, In r W -> L5.in_rng r a -> 0x10000 <= a < 0x633000 /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a)
    XB Mc modelc LKc crc Ac (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) K :
  L5AUK.cinv L ar HI M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac -> 0 <= Scr ->
  msteps RSEGS (st fx R pc (mrestrict (ahid Ac modelc) Mc)) (st fx1 R1 pc1 (mrestrict (ahid Ac modelc) Mc)) ->
  (forall model1, L5AUK.cinv L ar HI M0 model0 A0 LB FF Sp Scr W XB Mc model1 LKc crc Ac -> ahid Ac model1 = ahid Ac modelc ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pc1 Mc model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R pc Mc modelc) K.
Proof.
  intros CI HS0 MS KONT.
  apply (L5AUK.cinv_piece L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W WIMG XB Mc modelc LKc crc Ac fx fx1 R pc R1 pc1 _ (fun _ => False) K CI HS0 MS (mem_grows_refl _)).
  - intros a _ _. reflexivity.
  - intros a [].
  - intros M1 model1 CI1 AH _ FRM. assert (E : M1 = Mc). { apply mem_eq_of_agree. intros a Ha. apply FRM. exact Ha. intros []. } subst M1. exact (KONT model1 CI1 AH).
Qed.

(* [comment removed for export] *)
Lemma opdel_ag (UNWL : L5USA.as0_unw_layout L) (LB : list (Z * Z)) (FF : list fframe) (XB' : list (Z * Z)) (sp' scr : Z) (Mc M' : word -> option byte) :
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (XB' ++ LB) FF sp' scr a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> ahl_ceil ar <= sp' - scr -> 0 <= scr ->
  forall a k, 0 <= a -> a + k <= 2 ^ 64 -> ccl XB' sp' a k -> L5C.agree_on Mc M' a k.
Proof.
  intros FRM HC HS a k Ha Hk CL i Hi. apply FRM. clear - Ha Hk Hi; lia. exact (ccl_client L ar C LY UNWL LB FF XB' sp' scr a k i HC HS CL Hi).
Qed.

(* [comment removed for export] *)
Lemma cinv_nodup M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac :
  L5AUK.cinv L ar HI M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac -> base.NoDup (map fst (XB ++ LB)).
Proof. intros (HH & _). pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WFX. do 10 apply proj2 in WFX. exact (proj1 WFX). Qed.
Lemma nodup_neq (x y : Z) (l : list Z) : base.NoDup (x :: l) -> In y l -> x <> y.
Proof. intros ND Hy E. subst y. apply list_relations.list.NoDup_cons in ND. destruct ND as [X _]. apply X. apply base.list_elem_of_In. exact Hy. Qed.
Lemma nodup_tl (x : Z) (l : list Z) : base.NoDup (x :: l) -> base.NoDup l.
Proof. intros ND. apply list_relations.list.NoDup_cons in ND. exact (proj2 ND). Qed.

Section RB.
Variables (M0 : word -> option byte) (model0 : Model) (A0 : list (Z * Z)) (LB : list (Z * Z)) (FFr : list fframe) (Sp Scr : Z) (W : list L5.range) (F k rs : Z).
Local Notation FF' := ((F, k, rs) :: FFr).
Local Abbreviation cinv' := (L5AUK.cinv L ar HI M0 model0 A0 LB FF' Sp Scr W).
Variables (XB : list (Z * Z)) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)).
Hypothesis CI : cinv' XB Mc modelc LKc crc Ac.
Hypothesis Hk : In k [1; 2; 3].
Local Notation MV := (mrestrict (ahid Ac modelc) Mc).

(* [comment removed for export] *)
Lemma cu_fs_u64 a v : ar_fs ar <= a -> a + 8 <= ar_fs ar + FS_BYTES -> L5.u64_at RSEGS MV a v -> L5.u64_at RSEGS Mc a v.
Proof.
  intros H1 H2 X. pose proof (fr_num L ar C HI LY HIok M0 model0 A0 LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk) as (_ & _ & _ & N4 & _ & _ & N7 & _). destruct CI as (HH & _).
  pose proof (vis_pack L ar C HI LY HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & VFS & _).
  apply (proj1 (u64_at_vis _ Mc a v (VFS a 8 H1 H2) ltac:(clear - H1 N4; lia) ltac:(clear - H2 N7; lia))). exact X.
Qed.
Lemma cu_fs_u8 a v : ar_fs ar <= a -> a + 1 <= ar_fs ar + FS_BYTES -> L5.u8_at RSEGS MV a v -> L5.u8_at RSEGS Mc a v.
Proof.
  intros H1 H2 X. pose proof (fr_num L ar C HI LY HIok M0 model0 A0 LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk) as (_ & _ & _ & N4 & _ & _ & N7 & _). destruct CI as (HH & _).
  pose proof (vis_pack L ar C HI LY HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & VFS & _).
  apply (proj1 (u8_at_vis _ Mc a v (VFS a 1 H1 H2) ltac:(clear - H1 N4; lia) ltac:(clear - H2 N7; lia))). exact X.
Qed.

(* [comment removed for export] *)
Lemma fsh_avis a n : F / 8 + SB <= a -> a + n <= F / 8 + SB + ff_bytes k / 8 -> avis (ahid Ac modelc) a n.
Proof.
  intros H1 H2. pose proof (fr_num L ar C HI LY HIok M0 model0 A0 LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB). destruct CI as (HH & _).
  pose proof (vis_pack L ar C HI LY HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & VFSSH & _). unfold FS_BYTES in *.
  apply (VFSSH a n). intros i Hi. unfold in_shadow_of, S.
  pose proof (Z.div_le_mono (ar_fs ar) F 8 ltac:(clear; lia) N1) as X1. pose proof (Z.div_le_mono (F + ff_bytes k - 1) (ar_fs ar + FS_BYTES - 1) 8 ltac:(clear; lia) ltac:(unfold FS_BYTES; clear - N2; lia)) as X2.
  assert (X3 : (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - N3 HB. destruct HB as [E|[E|E]]; rewrite E in *; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  unfold FS_BYTES in X2. clear - Hi H1 H2 X1 X2 X3. lia.
Qed.
Lemma cv_fsh_zeros a n : F / 8 + SB <= a -> a + n <= F / 8 + SB + ff_bytes k / 8 -> L5KA.zeros_at Mc a n -> L5KA.zeros_at MV a n.
Proof. intros H1 H2 X. apply (proj2 (zeros_at_vis _ Mc a n (fsh_avis a n H1 H2))). exact X. Qed.
Lemma cu_fsh_zeros a n : F / 8 + SB <= a -> a + n <= F / 8 + SB + ff_bytes k / 8 -> L5KA.zeros_at MV a n -> L5KA.zeros_at Mc a n.
Proof. intros H1 H2 X. apply (proj1 (zeros_at_vis _ Mc a n (fsh_avis a n H1 H2))). exact X. Qed.
Lemma cu_fsh_u8 a v : F / 8 + SB <= a -> a + 1 <= F / 8 + SB + ff_bytes k / 8 -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at RSEGS MV a v -> L5.u8_at RSEGS Mc a v.
Proof. intros H1 H2 H3 H4 X. apply (proj1 (u8_at_vis _ Mc a v (fsh_avis a 1 H1 H2) H3 H4)). exact X. Qed.
(* [comment removed for export] *)
Lemma byte_of_u8_0 (Mx : word -> option byte) a : L5.u8_at RSEGS Mx a 0 -> Mx (Z_to_bv 64 a) <> None -> Mx (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof.
  unfold L5.u8_at. cbn [rdn]. destruct (Mx (Z_to_bv 64 a)) as [b|]; [|intros _ X; exfalso; apply X; reflexivity]. intros H _.
  change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in H. inversion H. reflexivity.
Qed.
Lemma zeros3_of_u8 (Mx : word -> option byte) a : L5.defined Mx a 3 -> L5.u8_at RSEGS Mx a 0 -> L5.u8_at RSEGS Mx (a + 1) 0 -> L5.u8_at RSEGS Mx (a + 2) 0 -> L5KA.zeros_at Mx a 3.
Proof.
  intros D U0 U1 U2 i Hi. assert (C3 : i = 0 \/ i = 1 \/ i = 2) by (clear - Hi; lia). destruct C3 as [E|[E|E]]; subst i.
  - rewrite Z.add_0_r. apply byte_of_u8_0. exact U0. pose proof (D 0 ltac:(clear; lia)) as X. rewrite Z.add_0_r in X. exact X.
  - apply byte_of_u8_0. exact U1. apply (D 1). clear; lia.
  - apply byte_of_u8_0. exact U2. apply (D 2). clear; lia.
Qed.
(* [comment removed for export] *)
Hypothesis WIMG : forall r a, In r W -> L5.in_rng r a -> 0x10000 <= a < 0x633000 /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Lemma frame_shadow_agree a n : F / 8 + SB <= a -> a + n <= F / 8 + SB + ff_bytes k / 8 -> L5C.agree_on M0 Mc a n.
Proof.
  intros H1 H2. pose proof (fr_num L ar C HI LY HIok M0 model0 A0 LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB). unfold FS_BYTES in *.
  assert (F8 : (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ 0 <= F / 8 /\ F / 8 + ff_bytes k / 8 <= 17592186044416).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - N1 N2 N3 N4 N7 HB. destruct HB as [E|[E|E]]; rewrite E in *; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (cinv_ek_agree L ar HI M0 model0 A0 LB Sp Scr W FF' XB Mc modelc LKc crc Ac a n CI). unfold SB in H1; clear - H1 F8; lia. unfold SB in H2; clear - H2 F8; lia.
  intros i Hi. split. apply (fframe_shadow_client L ar LB FF' Sp Scr F k rs). left; reflexivity. unfold in_shadow_of, S. rewrite (proj1 F8). clear - Hi H1 H2. lia.
  intros r Hr X. destruct (WIMG r i Hr X) as (Y & _). unfold SB in H1. clear - Y Hi H1 F8. lia.
Qed.

(* [comment removed for export] *)
Lemma kept_u64 a v : F + 32 <= a -> a + 8 <= F + ff_bytes k - 8 -> L5.u64_at RSEGS M0 a v -> L5.u64_at RSEGS MV a v.
Proof.
  intros H1 H2 X. pose proof (fr_num L ar C HI LY HIok M0 model0 A0 LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB). unfold FS_BYTES in *.
  apply (cv_fs_u64 L ar C HI LY HIok M0 model0 A0 LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk). clear - H1 N1; lia. unfold FS_BYTES; clear - H2 N2; lia.
  apply (L5C.u64_at_agree RSEGS M0 Mc a v). 4: exact X. 2: clear - H1 N1 N4; lia. 2: clear - H2 N2 N7; lia.
  apply (frame_agree L ar C HI LY HIok M0 model0 A0 LB FFr Sp Scr W F k rs WIMG XB Mc modelc LKc crc Ac a 8 CI Hk). clear - H1; lia. exact H2. right; exact H1.
Qed.
Lemma u8_of_u64_lo (Mx : word -> option byte) a v : L5.u64_at RSEGS Mx a v -> L5.u8_at RSEGS Mx a (v mod 256).
Proof.
  unfold L5.u64_at, L5.u8_at. intros HU. unfold word_to_le_bytes in HU. change 8%nat with (Datatypes.S 7) in HU. cbn [Z_to_le_bytes] in HU.
  rewrite (rdn_head Mx (Z_to_bv 64 a) 7 _ _ HU). f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by Lia.lia. change (2 ^ 64) with (256 * 72057594037927936).
  rewrite Z.rem_mul_r by Lia.lia. rewrite Z.mul_comm, Z.mod_add by Lia.lia. rewrite Z.mod_mod by Lia.lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rb_agree (M1 : word -> option byte) (Wp Wc : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall a, Wp a -> Wc a \/ F <= a < F + ff_bytes k \/ F / 8 + SB <= a < F / 8 + SB + ff_bytes k / 8) ->
  forall a n, 0 <= a -> a + n <= 2 ^ 64 -> L5AUK.cvis ar LB XB a n -> (forall i, a <= i < a + n -> ~ Wc i) -> L5C.agree_on Mc M1 a n.
Proof.
  intros FRM WP a n Ha Hn CV NC i Hi.
  pose proof (fr_num L ar C HI LY HIok M0 model0 A0 LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB).
  pose proof (L5AUK.cinv_num L ar HI M0 model0 A0 LB FF' Sp Scr W _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  destruct CI as (HH & _). pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  unfold BIGSHADOW_LO, BIGSHADOW_HI in N6. unfold FS_BYTES in *.
  assert (D : 0 <= F / 8 /\ F / 8 + ff_bytes k / 8 <= 17592186044416 /\ 64 <= ff_bytes k).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - N1 N2 N4 N7 HB. destruct HB as [E|[E|E]]; rewrite E in *; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply FRM. clear - Ha Hn Hi; lia. intros Wa. destruct (WP i Wa) as [Y|Y]. exact (NC i Hi Y). unfold SB in Y.
  destruct CV as [[X1 X2]|[[X1 X2]|(q & m & Hin & X1 & X2)]].
  - clear - Y Hi X1 N1 N2 N5 SPT D. lia.
  - clear - Y Hi X1 X2 N1 N4 D. lia.
  - destruct (WB (q, m) Hin) as (BR & _ & _ & _ & _ & _ & BFS). cbn [fst snd] in BR, BFS. destruct BR as (_ & _ & _ & _ & _ & BAPP).
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BAPP. clear - Y Hi X1 X2 N1 N2 D BFS BAPP. lia.
Qed.
End RB.
(* [comment removed for export] *)
Section ACCK.
Variables (M : word -> option byte) (model : Model) (A : list (Z * Z)) (LB : list (Z * Z)) (Sp Scr : Z) (W : list L5.range).
Hypothesis WIMG : forall r a, In r W -> L5.in_rng r a -> 0x10000 <= a < 0x633000 /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Variables (FFa FFr : list fframe) (F k rs : Z) (Mb : word -> option byte) (modelb : Model) (Ab : list (Z * Z)).
Variables (XB : list (Z * Z)) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)).
Hypothesis AC : acc L ar M model A LB Sp Scr W FFa Mb modelb Ab.
Hypothesis SU : sufl L ar LB FFa ((F, k, rs) :: FFr).
Hypothesis CI : L5AUK.cinv L ar HI Mb modelb Ab LB ((F, k, rs) :: FFr) Sp Scr W XB Mc modelc LKc crc Ac.
Hypothesis Hk : In k [1; 2; 3].
Hypothesis Hin : In (F, k, rs) FFa.
Local Notation MV := (mrestrict (ahid Ac modelc) Mc).

Lemma acc_frame_agree a n : F <= a -> a + n <= F + ff_bytes k - 8 -> (a + n <= F + 24 \/ F + 32 <= a) -> L5C.agree_on M Mc a n.
Proof.
  intros H1 H2 H3. pose proof (fr_num L ar C HI LY HIok Mb modelb Ab LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB). unfold FS_BYTES in *.
  apply (acc_agree L ar HI M model A LB Sp Scr W FFa _ Mb modelb Ab XB Mc modelc LKc crc Ac a n AC SU CI). clear - H1 N1 N4; lia. clear - H2 N2 N7; lia.
  intros i Hi. split. apply (fframe_client L ar LB FFa Sp Scr F k rs). exact Hin. clear - Hi H1 H2 H3; lia.
  intros r Hr X. destruct (WIMG r i Hr X) as (Y & _). clear - Y Hi H1 N1 N4. lia.
Qed.
Lemma acc_kept_u64 a v : F + 32 <= a -> a + 8 <= F + ff_bytes k - 8 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v.
Proof.
  intros H1 H2 X. pose proof (fr_num L ar C HI LY HIok Mb modelb Ab LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB). unfold FS_BYTES in *.
  apply (cv_fs_u64 L ar C HI LY HIok Mb modelb Ab LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk). clear - H1 N1; lia. unfold FS_BYTES; clear - H2 N2; lia.
  apply (L5C.u64_at_agree RSEGS M Mc a v). 4: exact X. 2: clear - H1 N1 N4; lia. 2: clear - H2 N2 N7; lia.
  apply acc_frame_agree. clear - H1; lia. exact H2. right; exact H1.
Qed.
Lemma acc_kept_u8 a v : F + 32 <= a -> a + 1 <= F + ff_bytes k - 8 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS MV a v.
Proof.
  intros H1 H2 X. pose proof (fr_num L ar C HI LY HIok Mb modelb Ab LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB). unfold FS_BYTES in *.
  apply (cv_fs_u8 L ar C HI LY HIok Mb modelb Ab LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk). clear - H1 N1; lia. unfold FS_BYTES; clear - H2 N2; lia.
  apply (L5C.u8_at_agree RSEGS M Mc a v). 4: exact X. 2: clear - H1 N1 N4; lia. 2: clear - H2 N2 N7; lia.
  apply acc_frame_agree. clear - H1; lia. exact H2. right; exact H1.
Qed.
Lemma acc_shadow_defined : L5.defined M (F / 8 + SB) (ff_bytes k / 8) -> L5.defined Mc (F / 8 + SB) (ff_bytes k / 8).
Proof.
  intros D. pose proof (fr_num L ar C HI LY HIok Mb modelb Ab LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB). unfold FS_BYTES in *.
  assert (F8 : (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ 0 <= F / 8 /\ F / 8 + ff_bytes k / 8 <= 17592186044416).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - N1 N2 N3 N4 N7 HB. destruct HB as [E|[E|E]]; rewrite E in *; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (acc_defined L ar HI M model A LB Sp Scr W FFa _ Mb modelb Ab XB Mc modelc LKc crc Ac _ _ AC SU CI). unfold SB; clear - F8; lia. unfold SB; clear - F8; lia. 2: exact D.
  intros i Hi. apply (fframe_shadow_client L ar LB FFa Sp Scr F k rs). exact Hin. unfold in_shadow_of, S. rewrite (proj1 F8). clear - Hi. lia.
Qed.
End ACCK.

End WithIface.
End SCFG_1.
(* [comment removed for export] *)
Tactic Notation "pure_step" constr(CI) constr(WIMG) ident(P) ident(fxn) ident(Rn) ident(modeln) ident(CIn) :=
  let Mv := fresh "Mv" in let FA := fresh "FA" in let MS := fresh "MS" in let EX := fresh "EX" in let AH := fresh "AH" in
  destruct P as (fxn & Rn & Mv & _ & FA & _ & (MS & EX));
  apply FunctionalExtensionality.functional_extensionality in FA; subst Mv;
  with_ci CI ltac:(fun L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac =>
    lazymatch goal with HS0 : 0 <= Scr |- srealizes _ _ _ ?K =>
      apply (cinv_pure L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W WIMG XB Mc modelc LKc crc Ac _ fxn _ _ Rn _ K CI HS0 MS);
      intros modeln CIn AH; clear MS;
      repeat match goal with H : context [ahid Ac modelc] |- _ => tryif constr_eq H AH then fail else rewrite <- AH in H end;
      repeat (lazymatch type of EX with _ /\ _ => let X := fresh "EX" in destruct EX as [X EX] end)
    end).
End L5AUK4.

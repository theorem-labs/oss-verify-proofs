(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed Hva, Hve, Tz_byte and 176 more; added Hlau, Hvl, brk and 10 more; removed av, ev, hw and 2 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/MuslStrlen.v, 424 lines within its lines 132-837. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From Stdlib Require FunctionalExtensionality. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module MemSplit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_MemSplit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List=repeat_lengthK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK47Corelib4Init9Datatypes6option01K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz02C49OSSVerify5KrLib8PropExec6u_add1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z8sub_diagC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega5Tauto8GFormula06I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums8positive03C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib7Mh_00387CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decc59OSSVerify5KrLib7Mh_00568MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00568MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK47Corelib4Init9Datatypes4bool02C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c59OSSVerify5KrLib7Mh_00568MemSplit6in_winC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc59OSSVerify5KrLib7Mh_00568MemSplit3wfJC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00568MemSplit;agree_aboveC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC59OSSVerify5KrLib7Mh_00387CatExecBstack_max_size_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00568MemSplit6win_loC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebK46Stdlib9micromega5Tauto8GFormula01c59OSSVerify5KrLib7Mh_00568MemSplit=wbytes_selectC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula02c59OSSVerify5KrLib7Mh_00568MemSplit?wbytes_select_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00568MemSplit4cmemC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02c59OSSVerify5KrLib7Mh_00568MemSplitBstack_max_size_posC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6leb_gtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atc59OSSVerify5KrLib7Mh_00568MemSplit;cmem_at_winC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_wsegC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z6ltb_ltI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_inside : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
  wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
  cbn [wbytes length] in *.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Z.sub_diag. cbn [Z.to_nat nth].
    destruct rest as [|b' rest'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in Hnw. rewrite wbytes_below.
      * rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by lia. cbn [length]. lia.
      * rewrite u_add1 by lia. lia.
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
      by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
    rewrite Hu1.
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
      with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

Lemma wbytes_outside : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x) ->
  wbytes m a bs x = m x.
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
Lemma wbytes_select : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
                    P x = true) ->
  wbytes (fun x => if P x then f x else g x) a bs
  = (fun x => if P x then wbytes f a bs x else g x).
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

Lemma wbytes_select_r : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
                    P x = false) ->
  wbytes (fun x => if P x then f x else g x) a bs
  = (fun x => if P x then f x else wbytes g a bs x).
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wbytes_shadow : forall m (a : word) bs1 bs2,
  length bs1 = length bs2 ->
  bv_unsigned a + Z.of_nat (length bs2) <= 2^64 ->
  wbytes (wbytes m a bs1) a bs2 = wbytes m a bs2.
Proof.
  intros m a bs1 bs2 Hlen Hnw. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs2))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_const : forall segs m (a : word) n b,
  bv_unsigned a + Z.of_nat n <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> m x = Some b) ->
  rdn segs m a n = Some (repeat b n).
Proof.
  intros segs m a n; revert a; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  cbn [rdn repeat]. rewrite (Hall a) by lia.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition win_lo (sp0 : word) : Z := bv_unsigned sp0 - stack_max_size.

(* [comment removed for export] *)
Definition wok_lo (sp0 : word) : Z :=
  bv_unsigned sp0 + stack_window_reach - stack_max_size.

Definition in_win (sp0 : word) (x : word) : Prop :=
  wok_lo sp0 <= bv_unsigned x < bv_unsigned sp0.

Lemma win_lo_le_wok_lo : forall sp0, win_lo sp0 <= wok_lo sp0.
Proof. intros. unfold win_lo, wok_lo, stack_window_reach. lia. Qed.

Definition cmem (sp0 : word) (mem0 J D : word -> option byte) : word -> option byte :=
  fun a => if (bv_unsigned sp0 <=? bv_unsigned a) then mem0 a
           else if (win_lo sp0 <=? bv_unsigned a) then J a else D a.

(* [comment removed for export] *)
Definition wfJ (sp0 : word) (J : word -> option byte) : Prop :=
  forall x : word, in_win sp0 x -> J x <> None.

Lemma wfJ_const : forall sp0 b, wfJ sp0 (fun _ => Some b).
Proof. intros sp0 b x _. discriminate. Qed.

Lemma wfJ_wbytes : forall sp0 J a bs, wfJ sp0 J -> wfJ sp0 (wbytes J a bs).
Proof. intros sp0 J a bs H x Hx. apply wbytes_grows. apply H. exact Hx. Qed.

(* [comment removed for export] *)
Definition stack_zero (lo : Z) : word -> option byte :=
  fun x => if lo <=? bv_unsigned x then Some (Z_to_bv 8 0) else None.

Lemma wfJ_stack_zero : forall inp (sp0 brk0 mbase : word) (rdraw : EntryDraw),
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
  wfJ sp0 (stack_zero (stack_window_lo (in_kernel inp) mbase rdraw)).
Proof.
  intros inp sp0 brk0 mbase rdraw Hvl Hlau x Hx. unfold in_win, wok_lo in Hx.
  pose proof (stack_window_lo_valid inp sp0 brk0 mbase rdraw Hvl Hlau).
  unfold stack_zero. rewrite (proj2 (Z.leb_le _ _)) by lia. discriminate.
Qed.

(* [comment removed for export] *)
Lemma stack_zero_in_win :
  forall inp (sp0 brk0 mbase : word) (rdraw : EntryDraw) (x : word),
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
  in_win sp0 x ->
  stack_zero (stack_window_lo (in_kernel inp) mbase rdraw) x
  = Some (Z_to_bv 8 0).
Proof.
  intros inp sp0 brk0 mbase rdraw x Hvl Hlau Hx. unfold in_win, wok_lo in Hx.
  pose proof (stack_window_lo_valid inp sp0 brk0 mbase rdraw Hvl Hlau).
  unfold stack_zero. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition agree_above (lo : Z) (J J' : word -> option byte) : Prop :=
  forall x : word, lo <= bv_unsigned x -> J' x = J x.

Lemma agree_above_refl : forall lo J, agree_above lo J J.
Proof. intros lo J x _. reflexivity. Qed.

Lemma agree_above_trans : forall lo J1 J2 J3,
  agree_above lo J1 J2 -> agree_above lo J2 J3 -> agree_above lo J1 J3.
Proof. intros lo J1 J2 J3 H12 H23 x Hx. rewrite (H23 x Hx). apply H12. exact Hx. Qed.

Lemma agree_above_mono : forall lo lo' J J',
  lo <= lo' -> agree_above lo J J' -> agree_above lo' J J'.
Proof. intros lo lo' J J' Hle H x Hx. apply H. lia. Qed.

Lemma agree_above_wbytes : forall lo J a bs,
  bv_unsigned a + Z.of_nat (length bs) <= lo ->
  agree_above lo J (wbytes J a bs).
Proof.
  intros lo J a bs Hle x Hx. apply wbytes_above. lia.
Qed.

Lemma rdn_agree_above : forall segs lo J J' (a : word) n,
  agree_above lo J J' -> lo <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= 2^64 ->
  rdn segs J' a n = rdn segs J a n.
Proof.
  intros segs lo J J' a n H Hlo Hnw. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply H. lia.
Qed.

Section CMem.
  Variable sp0 : word.
  Variable mem0 : word -> option byte.

  Let csel := cmem sp0 mem0.

  Lemma stack_max_size_pos : 0 < stack_max_size.
  Proof. rewrite stack_max_size_val. lia. Qed.

  (* [comment removed for export] *)

  Lemma wbytes_cmem_win : forall J D (a : word) bs,
    win_lo sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned sp0 ->
    wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 (wbytes J a bs) D.
  Proof.
    intros J D a bs Hlo Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if win_lo sp0 <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select (fun x => win_lo sp0 <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_le; lia]).
    reflexivity.
  Qed.

  Lemma wbytes_cmem_data : forall J D (a : word) bs,
    bv_unsigned a + Z.of_nat (length bs) <= win_lo sp0 ->
    wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 J (wbytes D a bs).
  Proof.
    intros J D a bs Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp. pose proof stack_max_size_pos.
    unfold win_lo in *.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if bv_unsigned sp0 - stack_max_size <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 - stack_max_size <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_gt; lia]).
    reflexivity.
  Qed.

  (* [comment removed for export] *)

  Lemma rdn_cmem_above : forall segs J D (a : word) n,
    bv_unsigned sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= 2^64 ->
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs mem0 a n.
  Proof.
    intros segs J D a n Hlo Hnw. apply rdn_ext; [exact Hnw|].
    intros x Hx. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma rdn_cmem_win : forall segs J D (a : word) n,
    win_lo sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 ->
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs J a n.
  Proof.
    intros segs J D a n Hlo Hhi. pose proof (u64_range sp0).
    apply rdn_ext; [lia|].
    intros x Hx. unfold cmem.
    rewrite (proj2 (Z.leb_gt _ _)) by lia.
    rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma rdn_cmem_data : forall segs J D (a : word) n,
    bv_unsigned a + Z.of_nat n <= win_lo sp0 ->
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs D a n.
  Proof.
    intros segs J D a n Hhi. pose proof (u64_range sp0). pose proof stack_max_size_pos.
    unfold win_lo in *.
    apply rdn_ext; [lia|].
    intros x Hx. unfold cmem, win_lo.
    rewrite (proj2 (Z.leb_gt _ _)) by lia.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cmem_at_above : forall J D (x : word),
    bv_unsigned sp0 <= bv_unsigned x -> cmem sp0 mem0 J D x = mem0 x.
  Proof. intros. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. Qed.

  Lemma cmem_at_win : forall J D (x : word),
    in_win sp0 x -> cmem sp0 mem0 J D x = J x.
  Proof.
    intros J D x [Hlo Hhi]. pose proof (win_lo_le_wok_lo sp0). unfold cmem.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma cmem_at_data : forall J D (x : word),
    bv_unsigned x < win_lo sp0 -> cmem sp0 mem0 J D x = D x.
  Proof.
    intros J D x Hx. pose proof stack_max_size_pos. unfold cmem, win_lo in *.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)

  Lemma store_ok_cmem_win : forall segs J D (a : word) n,
    wfJ sp0 J ->
    wok_lo sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 ->
    store_ok segs (cmem sp0 mem0 J D) a n = true.
  Proof.
    intros segs J D a n HJ Hlo Hhi. pose proof (u64_range sp0).
    pose proof (win_lo_le_wok_lo sp0).
    apply store_ok_of_all; [lia|].
    intros x Hx. unfold wview.
    rewrite cmem_at_win by (unfold in_win; lia).
    destruct (J x) as [b|] eqn:E; [discriminate|].
    exfalso. apply (HJ x); [unfold in_win; lia | exact E].
  Qed.

  Lemma store_ok_cmem_data : forall segs J D (a : word) n,
    wseg_ok segs a n = true ->
    store_ok segs (cmem sp0 mem0 J D) a n = true.
  Proof. intros. apply store_ok_wseg. assumption. Qed.

End CMem.

(* [comment removed for export] *)
Lemma cmem_init :
  forall inp mbase ph entry (sp0 brk0 : word) (rdraw : EntryDraw),
  entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
  wrap_mem inp mbase ph entry sp0 rdraw
  = cmem sp0 (wrap_mem inp mbase ph entry sp0 rdraw)
      (stack_zero (stack_window_lo (in_kernel inp) mbase rdraw))
      (fun _ => None).
Proof.
  intros inp mbase ph entry sp0 brk0 rdraw Hlau.
  apply functional_extensionality. intro x.
  pose proof (stack_window_lo_ge_sp inp sp0 brk0 mbase rdraw Hlau) as Hge.
  unfold cmem.
  destruct (bv_unsigned sp0 <=? bv_unsigned x) eqn:E1; [reflexivity|].
  apply Z.leb_gt in E1.
  unfold wrap_mem, win_lo, stack_zero.
  assert (Hst : stack_to_mem sp0 (entry_stack_image inp mbase ph entry sp0 rdraw) x
                = None).
  { unfold stack_to_mem. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
  rewrite Hst. rewrite (proj2 (Z.ltb_lt _ _) E1), andb_true_r.
  destruct (bv_unsigned sp0 - stack_max_size <=? bv_unsigned x) eqn:E2;
    [reflexivity|].
  apply Z.leb_gt in E2.
  rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.
End MemSplit.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_RefMemcpyLib () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib3subC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List=repeat_lengthI47Corelib4Init9Datatypes4list00C47Corelib4Init3Nat3addC47Corelib5Lists7ListDef5skipnI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib:firstn_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib>firstn_sub_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9skipn_addC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List<length_skipnI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z8min_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=length_firstnC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib:sub_lengthC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List:firstn_allc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9sub_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9sub_0_allC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib@length_firstn_idC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init5Peano2ltC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1Z02C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedC59OSSVerify5KrLib7Mh_00385Hoare3at_C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00K47Corelib4Init5Logic4True01C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC59OSSVerify5KrLib7Mh_00385Hoare4at_0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib7at_succC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic8iff_reflC59OSSVerify5KrLib7Mh_00385Hoare5at_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib<word_succ_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC56Stdlib5Arith8PeanoNat3Nat;le_gt_casesc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib:wbytes_appC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib=wbytes_extendC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9rdn_skipnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC56Stdlib6ZArith6BinInt1Z3mulC49OSSVerify5KrLib8PropExecDbytes_le_to_Z_nonnegC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecCbytes_le_to_Z_boundC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib=lez_bound_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib:lez4_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z4of_NC35stdpp9decidable;bool_decideC35stdpp9decidableCbool_decide_reflectI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega5Tauto8GFormula07C45stdpp9bitvector;definitions=bv_swrap_specC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC45stdpp9bitvector;definitions@bv_wrap_spec_lowc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib6u_lez4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib3LWvC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC45stdpp7numbers1Z6lt_decC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z;lt_ge_casesc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib=testbit_u_LWvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC49OSSVerify5KrLib8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1ZBmod_pow2_bits_highC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3lorK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z6bits_0C47Corelib4Init9Datatypes3orbC49OSSVerify5KrLib8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z;shiftl_specC56Stdlib6ZArith6BinInt1Z8lor_specc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib8lez_consC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z=testbit_neg_rC46Stdlib4Bool4Bool;orb_false_rc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib@testbit_lez_highC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<bytes_le_appC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z6shiftrc59OSSVerify5KrLib7Mh_0056<RefMemcpyLibAtestbit_lez_skipnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;shiftr_specC45stdpp9bitvector;definitionsAbv_wrap_spec_highc59OSSVerify5KrLib7Mh_0056<RefMemcpyLibAZ_to_le_bytes_lezC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExecBZ_to_le_bytes_wrapC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc59OSSVerify5KrLib7Mh_0056<RefMemcpyLibEword_to_le_bytes_4_eqC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions=bv_wrap_smallc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib3LBvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib?testbit_nth_lezC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib:sb_byte_eqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:C49OSSVerify5KrLib8PropExec7v_srliwC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto4kind02C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appc59OSSVerify5KrLib7Mh_0056<RefMemcpyLibBtestbit_lez_firstnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib?testbit_lez_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLibCtestbit_u_srliw_LWvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLibBtestbit_u_slli_LWvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib=testbit_u_vorC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_commc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib>sw_bytes_mergeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib4at_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib:keeps_getrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_eq_decC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C49OSSVerify5KrLib8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_ind".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sub {A} (bs : list A) (j k : nat) : list A := firstn k (skipn j bs).

Lemma firstn_add : forall {A} (l : list A) a b,
  firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b.
  - cbn. reflexivity.
  - destruct l as [|x l]; cbn.
    + destruct b; reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma firstn_sub_app : forall {A} (bs : list A) j k,
  firstn j bs ++ sub bs j k = firstn (j + k) bs.
Proof. intros. unfold sub. rewrite firstn_add. reflexivity. Qed.

Lemma skipn_add : forall {A} (l : list A) a b, skipn (a + b) l = skipn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity|]. apply IH.
Qed.

Lemma sub_length : forall {A} (bs : list A) j k,
  (j + k <= length bs)%nat -> length (sub bs j k) = k.
Proof.
  intros A bs j k H. unfold sub. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma sub_split : forall {A} (bs : list A) j a b,
  sub bs j (a + b) = sub bs j a ++ sub bs (j + a) b.
Proof.
  intros A bs j a b. unfold sub. rewrite firstn_add. f_equal.
  rewrite <- skipn_add. f_equal; lia.
Qed.

Lemma sub_0_all : forall {A} (bs : list A), sub bs 0 (length bs) = bs.
Proof. intros. unfold sub. cbn. apply firstn_all. Qed.

Lemma length_firstn_id : forall {A} (bs : list A) k, k = length bs -> firstn k bs = bs.
Proof. intros A bs k ->. apply firstn_all. Qed.

Lemma sub_nth : forall (bs : list byte) j,
  (j < length bs)%nat -> sub bs j 1 = [nth j bs (Z_to_bv 8 0)].
Proof.
  intros bs j. revert bs. induction j as [|j IH]; intros bs H.
  - destruct bs; cbn in *; [lia|reflexivity].
  - destruct bs; cbn in *; [lia|]. unfold sub in IH. apply IH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma at_succ : forall (a : word) d, (at_ a d + 1)%bv = at_ a (d + 1).
Proof.
  intros a d. unfold at_. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1 : word)) with 1.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_succ_at : forall (a : word), (a + 1)%bv = at_ a 1.
Proof. intros a. rewrite <- (at_0 a) at 1. rewrite at_succ. reflexivity. Qed.

Lemma at_u : forall (a : word) d,
  0 <= bv_unsigned a + d -> bv_unsigned a + d < 2^64 ->
  bv_unsigned (at_ a d) = bv_unsigned a + d.
Proof. intros a d H1 H2. unfold at_. apply u_Z2bv; lia. Qed.

Lemma at_nat : forall (a : word) (j : nat), (a + nat_to_word j)%bv = at_ a (Z.of_nat j).
Proof.
  intros a j. unfold at_, nat_to_word. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_app : forall bs1 bs2 m (a : word),
  wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (at_ a (Z.of_nat (length bs1))) bs2.
Proof.
  induction bs1 as [|b r IH]; intros bs2 m a.
  - cbn [app wbytes length Z.of_nat]. rewrite at_0. reflexivity.
  - cbn [app wbytes length]. rewrite IH. f_equal.
    rewrite word_succ_at, at_at. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_extend : forall m (dst : word) bs j k,
  wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
  = wbytes m dst (firstn (j + k) bs) \/ (length bs < j)%nat.
Proof.
  intros m dst bs j k.
  destruct (Nat.le_gt_cases j (length bs)) as [H|H]; [left|right; exact H].
  rewrite <- firstn_sub_app, wbytes_app. rewrite length_firstn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma wbytes_extend' : forall m (dst : word) bs j k,
  (j <= length bs)%nat ->
  wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
  = wbytes m dst (firstn (j + k) bs).
Proof.
  intros m dst bs j k H. destruct (wbytes_extend m dst bs j k) as [E|E]; [exact E|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : forall segs mem n (a : word) bs j,
  rdn segs mem a n = Some bs -> (j <= n)%nat ->
  rdn segs mem (at_ a (Z.of_nat j)) (n - j) = Some (skipn j bs).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs j H Hj.
  - assert (j = 0)%nat by lia. subst j. cbn in H. injection H as <-.
    rewrite at_0. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1)%bv n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct j as [|j].
    + rewrite at_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn]. replace (S n - S j)%nat with (n - j)%nat by lia.
      replace (at_ a (Z.of_nat (S j))) with (at_ (a + 1)%bv (Z.of_nat j))
        by (rewrite word_succ_at, at_at; f_equal; lia).
      apply IH; [exact Er|lia].
Qed.

Lemma rdn_sub : forall segs mem n (a : word) bs j k,
  rdn segs mem a n = Some bs -> (j + k <= n)%nat ->
  rdn segs mem (at_ a (Z.of_nat j)) k = Some (sub bs j k).
Proof.
  intros segs mem n a bs j k H Hjk. unfold sub.
  apply (rdn_firstn segs mem (n - j)); [|lia].
  apply rdn_skipn; [exact H|lia].
Qed.
End FPX_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Abbreviation lez := bytes_le_to_Z.
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition LWv (l : list byte) : word := v_lw (Z_to_bv 64 (lez l)).

Lemma lez_bound_len : forall bs k, length bs = k -> 0 <= lez bs < 2 ^ (8 * Z.of_nat k).
Proof. intros bs k <-. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound]. Qed.
Lemma lez4_range : forall l, length l = 4%nat -> 0 <= lez l < 2 ^ 32.
Proof. intros l H. pose proof (lez_bound_len l 4%nat H). change (8 * Z.of_nat 4) with 32 in H0. lia. Qed.
Lemma u_lez4 : forall l, length l = 4%nat -> bv_unsigned (Z_to_bv 64 (lez l)) = lez l.
Proof. intros l H. pose proof (lez4_range l H). apply u_Z2bv; lia. Qed.

Lemma testbit_u_LWv : forall l i, length l = 4%nat -> 0 <= i < 32 ->
  Z.testbit (bv_unsigned (LWv l)) i = Z.testbit (lez l) i.
Proof.
  intros l i H Hi. unfold LWv, v_lw. rewrite Z_to_bv_unsigned, u_lez4 by exact H.
  rewrite bv_wrap_spec_low by lia.
  rewrite bv_swrap_spec by lia.
  case_bool_decide; [reflexivity|].
  replace i with 31 by lia. reflexivity.
Qed.

Lemma u_vlw_mod32 : forall l, length l = 4%nat -> bv_unsigned (LWv l) mod 2 ^ 32 = lez l.
Proof.
  intros l H. pose proof (lez4_range l H) as R.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32) as [Hl|Hh].
  - rewrite Z.mod_pow2_bits_low by lia. apply testbit_u_LWv; [exact H|lia].
  - rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (Z_testbit_high 32); lia.
Qed.

Lemma lez_cons : forall b bs, lez (b :: bs) = Z.lor (bv_unsigned b) (Z.shiftl (lez bs) 8).
Proof. reflexivity. Qed.

Lemma testbit_lez_high : forall bs i, 8 * Z.of_nat (length bs) <= i -> Z.testbit (lez bs) i = false.
Proof.
  intros bs i Hi. apply (Z_testbit_high (8 * Z.of_nat (length bs))); try lia.
  apply lez_bound_len. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_lez_skipn : forall q bs i, 0 <= i ->
  Z.testbit (lez (skipn q bs)) i = Z.testbit (lez bs) (i + 8 * Z.of_nat q).
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [skipn]. f_equal. lia.
  - destruct bs as [|b bs].
    + cbn [skipn lez]. rewrite !Z.bits_0. reflexivity.
    + cbn [skipn]. rewrite IH by lia. rewrite lez_cons.
      rewrite Z.lor_spec, Z.shiftl_spec by lia.
      pose proof (u8_range b).
      rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. cbn [orb]. f_equal. lia.
Qed.

Lemma testbit_lez_firstn : forall q bs i, 0 <= i ->
  Z.testbit (lez (firstn q bs)) i = if i <? 8 * Z.of_nat q then Z.testbit (lez bs) i else false.
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [firstn lez]. rewrite Z.bits_0. destruct (Z.ltb_spec i (8 * Z.of_nat 0)); [lia|reflexivity].
  - destruct bs as [|b bs].
    + cbn [firstn lez]. rewrite !Z.bits_0. destruct (i <? _); reflexivity.
    + cbn [firstn]. rewrite !lez_cons, !Z.lor_spec, !Z.shiftl_spec by lia.
      destruct (Z.lt_ge_cases i 8) as [H8|H8].
      * rewrite !(Z.testbit_neg_r _ (i - 8)) by lia.
        destruct (Z.ltb_spec i (8 * Z.of_nat (S q))); [reflexivity|lia].
      * rewrite IH by lia.
        destruct (Z.ltb_spec (i - 8) (8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (S q))); try lia; try reflexivity.
        pose proof (u8_range b). rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. reflexivity.
Qed.

Lemma testbit_lez_app : forall xs ys i, 0 <= i ->
  Z.testbit (lez (xs ++ ys)) i =
  if i <? 8 * Z.of_nat (length xs) then Z.testbit (lez xs) i else Z.testbit (lez ys) (i - 8 * Z.of_nat (length xs)).
Proof.
  intros xs ys i Hi. rewrite bytes_le_app, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i (8 * Z.of_nat (length xs))).
  - rewrite (Z.testbit_neg_r (lez ys)) by lia. apply orb_false_r.
  - rewrite testbit_lez_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_lez : forall bs, Z_to_le_bytes (length bs) (lez bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes].
  replace (Z.shiftr (lez (b :: bs)) 8) with (lez bs).
  2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec by lia.
      pose proof (testbit_lez_skipn 1 (b :: bs) i Hi) as E. change (skipn 1 (b :: bs)) with bs in E.
      rewrite E. reflexivity. }
  rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. rewrite lez_cons, Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma word_to_le_bytes_4_eq : forall (v : word) (l : list byte),
  length l = 4%nat ->
  (forall i, 0 <= i < 32 -> Z.testbit (bv_unsigned v) i = Z.testbit (lez l) i) ->
  word_to_le_bytes 4 v = l.
Proof.
  intros v l Hl Hb. unfold word_to_le_bytes.
  rewrite <- (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
  rewrite <- Hl at 1. rewrite <- (Z_to_le_bytes_lez l). rewrite Hl. f_equal.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply testbit_lez_high. rewrite Hl. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_LWv : forall l, length l = 4%nat -> word_to_le_bytes 4 (LWv l) = l.
Proof.
  intros l H. apply word_to_le_bytes_4_eq; [exact H|]. intros i Hi. apply testbit_u_LWv; assumption.
Qed.

(* [comment removed for export] *)
Definition LBv (b : byte) : word := Z_to_bv 64 (bv_unsigned b).

Lemma sb_byte_LBv : forall b : byte, Z_to_bv 8 (bv_unsigned (LBv b)) = b.
Proof.
  intros b. unfold LBv. pose proof (u8_range b). rewrite u_Z2bv by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_eq : forall (v : word) (b : byte),
  (forall i, 0 <= i < 8 -> Z.testbit (bv_unsigned v) i = Z.testbit (bv_unsigned b) i) ->
  Z_to_bv 8 (bv_unsigned v) = b.
Proof.
  intros v b Hb. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma testbit_nth_lez : forall l q i, 0 <= i < 8 -> (q < length l)%nat ->
  Z.testbit (bv_unsigned (nth q l (Z_to_bv 8 0))) i = Z.testbit (lez l) (i + 8 * Z.of_nat q).
Proof.
  intros l q i Hi Hq. rewrite <- testbit_lez_skipn by lia.
  revert l Hq. induction q as [|q IH]; intros l Hq.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. rewrite lez_cons.
    rewrite Z.lor_spec, Z.shiftl_spec, (Z.testbit_neg_r _ (i - 8)) by lia. symmetry. apply orb_false_r.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. apply IH. cbn in Hq. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_srli_LWv : forall l q, length l = 4%nat -> (q <= 3)%nat ->
  Z_to_bv 8 (bv_unsigned (v_srli (LWv l) (8 * Z.of_nat q))) = nth q l (Z_to_bv 8 0).
Proof.
  intros l q H Hq. apply sb_byte_eq. intros i Hi.
  unfold v_srli. rewrite Z_to_bv_unsigned, bv_wrap_spec_low, Z.shiftr_spec by lia.
  rewrite testbit_u_LWv by (try exact H; lia).
  rewrite testbit_nth_lez by (try rewrite H; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_u_srliw_LWv : forall l s i, length l = 4%nat -> 1 <= s -> 0 <= i ->
  Z.testbit (bv_unsigned (v_srliw (LWv l) s)) i = if i + s <? 32 then Z.testbit (lez l) (i + s) else false.
Proof.
  intros l s i H Hs Hi. unfold v_srliw. rewrite Z_to_bv_unsigned.
  assert (Sh : forall j, 0 <= j -> Z.testbit (Z.shiftr (bv_wrap 32 (bv_unsigned (LWv l))) s) j
                              = if j + s <? 32 then Z.testbit (lez l) (j + s) else false).
  { intros j Hj. rewrite Z.shiftr_spec by lia.
    destruct (Z.ltb_spec (j + s) 32).
    - rewrite bv_wrap_spec_low by lia. apply testbit_u_LWv; [exact H|lia].
    - apply bv_wrap_spec_high. lia. }
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. rewrite bv_swrap_spec by lia.
    case_bool_decide.
    + apply Sh. lia.
    + rewrite Sh by lia.
      destruct (Z.ltb_spec (Z.of_N 32 - 1 + s) 32), (Z.ltb_spec (i + s) 32); try lia; reflexivity.
  - rewrite bv_wrap_spec_high by lia. destruct (Z.ltb_spec (i + s) 32); [lia|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma testbit_u_slli_LWv : forall l s i, length l = 4%nat -> 0 <= s -> 0 <= i < 32 ->
  Z.testbit (bv_unsigned (v_slli (LWv l) s)) i = if i <? s then false else Z.testbit (lez l) (i - s).
Proof.
  intros l s i H Hs Hi. unfold v_slli. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_spec_low by lia. rewrite Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i s).
  - apply Z.testbit_neg_r. lia.
  - apply testbit_u_LWv; [exact H|lia].
Qed.

Lemma testbit_u_vor : forall (x y : word) i, 0 <= i ->
  Z.testbit (bv_unsigned (v_or x y)) i = Z.testbit (bv_unsigned x) i || Z.testbit (bv_unsigned y) i.
Proof.
  intros x y i Hi. unfold v_or. rewrite Z_to_bv_unsigned.
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. apply Z.lor_spec.
  - rewrite bv_wrap_spec_high by lia.
    pose proof (u64_range x). pose proof (u64_range y).
    rewrite (Z_testbit_high 64 (bv_unsigned x)) by lia. rewrite (Z_testbit_high 64 (bv_unsigned y)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_merge : forall l1 l2 (q : nat) (v : word),
  length l1 = 4%nat -> length l2 = 4%nat -> (1 <= q <= 3)%nat ->
  v = v_or (v_slli (LWv l2) (32 - 8 * Z.of_nat q)) (v_srliw (LWv l1) (8 * Z.of_nat q)) ->
  word_to_le_bytes 4 v = skipn q l1 ++ firstn q l2.
Proof.
  intros l1 l2 q v H1 H2 Hq ->.
  apply word_to_le_bytes_4_eq.
  { rewrite length_app, length_skipn, length_firstn, H1, H2. lia. }
  intros i Hi.
  rewrite testbit_u_vor by lia.
  rewrite testbit_u_slli_LWv by (try exact H2; lia).
  rewrite testbit_u_srliw_LWv by (try exact H1; lia).
  rewrite testbit_lez_app by lia. rewrite length_skipn, H1.
  rewrite testbit_lez_skipn by lia.
  destruct (Z.ltb_spec i (32 - 8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (4 - q))),
           (Z.ltb_spec (i + 8 * Z.of_nat q) 32); try lia.
  - reflexivity.
  - rewrite testbit_lez_firstn by lia.
    destruct (Z.ltb_spec (i - 8 * Z.of_nat (4 - q)) (8 * Z.of_nat q)); [|lia].
    rewrite orb_false_r. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_merge' : forall l1 l2 (q : nat) (v : word),
  length l1 = 4%nat -> length l2 = 4%nat -> (1 <= q <= 3)%nat ->
  v = v_or (v_srliw (LWv l1) (8 * Z.of_nat q)) (v_slli (LWv l2) (32 - 8 * Z.of_nat q)) ->
  word_to_le_bytes 4 v = skipn q l1 ++ firstn q l2.
Proof.
  intros l1 l2 q v H1 H2 Hq ->. apply (sw_bytes_merge l1 l2 q); try assumption.
  unfold v_or. f_equal. apply Z.lor_comm.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_at : forall segs m (dst : word) (N : nat) bsw j k,
  bv_unsigned dst + Z.of_nat N <= 2 ^ 64 ->
  store_ok segs m dst N = true ->
  0 <= j -> j + Z.of_nat k <= Z.of_nat N ->
  store_ok segs (wbytes m dst bsw) (at_ dst j) k = true.
Proof.
  intros segs m dst N bsw j k Hnw Hok Hj Hk.
  destruct k as [|k]; [reflexivity|].
  pose proof (u64_range dst).
  apply (store_ok_mono segs (S k) m); [apply wbytes_grows|].
  apply (store_ok_sub segs m dst (at_ dst j) N (S k) Hnw Hok); rewrite at_u; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition callee_kept : list reg :=
  [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_kept -> getr regs' r = getr regs r.

Lemma keeps_refl : forall regs, keeps regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_trans : forall r1 r2 r3, keeps r1 r2 -> keeps r2 r3 -> keeps r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

(* [comment removed for export] *)
Lemma keeps_upd : forall regs regs' (rd : reg) v,
  keeps regs regs' -> ~ In rd callee_kept -> keeps regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

(* [comment removed for export] *)
Lemma keeps_getr : forall regs regs' (r : reg), keeps regs regs' -> In r callee_kept -> getr regs' r = getr regs r.
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.
End FPX_2.


Ltac kept_reg := cbv [callee_kept In]; intuition congruence.
Section FPX_3. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Example keeps_sp_example : forall regs regs', keeps regs regs' -> getr regs' 2 = getr regs 2.
Proof.
ltac2:(KReplay.run1 (kr_t_RefMemcpyLib ()) ["FPX_3"] "h01Kh14regsh25regs'p;1p;2p;3p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9p1003<p4p710R0p1003Yp4p710R1p8P0p10045p4p710R0p8p1004Sp6051000R2p1005Pp4p710R3p8p100=@p6051000R4P3p8P4P0p8P4p1005op4p710R5p8p100>Dp6051000R6P1p8P6P3p8P6P2p8P6P4p8P6P5p8g006LR6p4p7210P0p8p100?Lp6051000R7P1p8P7P3p8p100g5p6051000R1P2p8P1p100@Op4p710R8p8P1p10078p4p710R1p8p100i5p6051000R9p100h9R:p4p710p8P9P:p4p7210p8P9P2p8P9P4p8P9P7p8P9P5p8p100j8p6051000R5P2p8P5P8p8P5P1p8p100k;p6051000R5P3p8P5P8p8P5P1p8P1P0p8p1007Wp4p710P0p8g00Oej11Tg00PJj12Tg00lEj17Tg00lcj18TP6j2ATg02ZDj2<Tg00n`j13Tg009Nj34Tg00IRj26Tg009hj29Tg01O<j3@Tg01OVj3?Tg02Y;j3>Tg02^4j5=Tg012^j35Tf1R6f0R0#3g018mR135p=;f3R5f2R8?561;40p=:f4%38=551;46/60p=0g00ePR5#1R1#2R3#7R2%11R9#1R7#1#1#1#7#8'AR41<60P8P61;21R1P0%82R0P2%35P1C:A4011R6P0P2%25R5P1P0P2P9P1P0P2P7P1P0P2%29R9P1P0P2%13R7P1P0P2%19P1P0P2%29P1P0P2%17P1P0P2%27P1P0P2%23R3#1P1P0P2%23P1P0P2%15R5#1R3#1P1P0P2%23P1P0P2%25R5#1P1P0P2%25P1g01TXD0D0D0D0D0D0D0D0D0D0D0D0D0D0D0R5'619019@653?g02[C9>01eD=W0X24W1o"). Qed.
End FPX_3.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wf_not_in_b : forall (r : reg) (l : list reg), forallb (fun x => negb (bv_eqb x r)) l = true -> ~ In r l.
Proof.
ltac2:(KReplay.run1 (kr_t_RefMemcpyLib ()) [] "p'0h01xh11Hh22H0h33Hinh41bi001bh51eh61lh75lemmah81rp;1p;3p;2p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9p1003<p4p710R0g003YR1p4p710R2p8P0p10045p4p710R0p8p1004Sp4p710R3p1005Pp4p710R4p8p100=@p4p710R5P4p8P5P0p8P5p1005op4p710R6p8p100>Dp4p710R7P2p8P7P4p8P7P3p8P7P5p8P7P6p8p1006Lp4p7210P0p8p100?Lp4p710R7P2p8P7P4p8p100g5p4p710R2P3p8P2p100@Op4p710R8p8P2p10078p4p710R2p8p100i5p4p710R9p100h9R:p4p710p8P9P:p4p7210p8P9P3p8P9P5p8P9P7p8P9P6p8p100j8p4p710R6P3p8P6P8p8P6P2p8p100k;p4p710R6P4p8P6P8p8P6P2p8P2P0p8p1007Wp4p710P0p8g00Oej1ATg00PJj1@Tg00lEj17Tg00lcj16Tg0089j1?Tg01ICj32Tg02_8j10Tg02_Vj33Tg02Y;j34Tg02`2j28Tg02`Kj39Tg02a<j3:Tg02a_j2>TP1j65Tg01RIj2<Tg01`Gj1;Tg009Nj3=Tg00f5R1f0R0g00fUR23=p=1g00eP#A#@#7R6#6R8%?8f2R49260#0X08=380#1f1R39484R9f4R79260#0X08R5=384#1f3R:9480f69260#0X08P3O1#1[^08R;'8f5R<9260#0X08=38:#1A4807f79260#0X08P3O1#1[^08;90W7A:854P3O2P;P0P7P3O2A2677#0#1P1A26<<%00#1X41P0P21>6<E5%02R<#1P1P<P1p-0P0g01TXR<g01Ehn0110000020000X51g018mP2P0E5P<1<<0b2b1b1b1W3%;9eW1W6W8o"). Qed.
Ltac not_kept := first [ apply wf_not_in_b; reflexivity | cbv; intuition discriminate ].

(* [comment removed for export] *)
Ltac solve_keeps :=
  repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Section FPX_4. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma runs_trans : forall segs (s0 : machine_state)
    (st1 : bvmap 5 word -> machine_state) (P1 : bvmap 5 word -> Prop)
    (st2 : bvmap 5 word -> machine_state) (P2 : bvmap 5 word -> Prop),
  (exists r1, msteps segs s0 (st1 r1) /\ P1 r1) ->
  (forall r1, P1 r1 -> exists r2, msteps segs (st1 r1) (st2 r2) /\ P2 r2) ->
  exists r2, msteps segs s0 (st2 r2) /\ P2 r2.
Proof.
  intros segs s0 st1 P1 st2 P2 (r1 & R1 & H1) K.
  destruct (K r1 H1) as (r2 & R2 & H2).
  exists r2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition callee_saved : list reg :=
  [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps_cs (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_saved -> getr regs' r = getr regs r.

Lemma keeps_cs_refl : forall regs, keeps_cs regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_cs_trans : forall r1 r2 r3, keeps_cs r1 r2 -> keeps_cs r2 r3 -> keeps_cs r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma keeps_cs_upd : forall regs regs' (rd : reg) v,
  keeps_cs regs regs' -> ~ In rd callee_saved -> keeps_cs regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

(* [comment removed for export] *)
Lemma keeps_cs_upd_same : forall regs regs' (rd : reg) v,
  keeps_cs regs regs' -> getr regs rd = v -> rd <> 0%bv -> keeps_cs regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hv Hnz r Hr.
  destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply K, Hr.
Qed.

Lemma keeps_keeps_cs : forall regs regs', keeps regs regs' -> keeps_cs regs regs'.
Proof.
  intros regs regs' K r Hr. apply K. unfold callee_saved, callee_kept in *. cbn [In] in *. intuition.
Qed.

Lemma keeps_cs_getr : forall regs regs' (r : reg), keeps_cs regs regs' -> In r callee_saved -> getr regs' r = getr regs r.
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.
End FPX_4.


Ltac solve_keeps_cs :=
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].

End RefMemcpyLib.
Module MemsetLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_MemsetLib () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib3subC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib:firstn_addC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib>firstn_sub_appC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9skipn_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib:sub_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9sub_splitC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9sub_0_allC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib@length_firstn_idC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib7Mh_00569MemsetLib6ms_inbC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib7Numbers7BinNums1Z00C47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib7Mh_00569MemsetLib6ms_covC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK47Corelib4Init5Logic2eq01C46Stdlib5Lists4List;existsb_appC46Stdlib5Lists4List2InC46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsc59OSSVerify5KrLib7Mh_00569MemsetLib;ms_inb_trueC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib7Mh_00569MemsetLib8ms_chainC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C46Stdlib5Lists4List4inclc59OSSVerify5KrLib7Mh_00569MemsetLib<ms_chain_covC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib9ms_cov_InC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib7Mh_00569MemsetLib5cfillC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z3subC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK47Corelib4Init9Datatypes4bool02C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8ltb_specK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04C47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms5flip2C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib7Mh_00385Hoare3at_C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib4at_uC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4BoolBnot_true_iff_falseC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib7Mh_00569MemsetLib;ms_cov_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00568MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3nthC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=nth_repeat_ltc59OSSVerify5KrLib7Mh_00568MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC47Corelib7Classes>Morphisms_Prop@not_iff_morphismI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationK46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib7Mh_00569MemsetLib?ms_cov_by_chainC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib:cfill_fullC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc59OSSVerify5KrLib7Mh_00569MemsetLib;cfill_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc59OSSVerify5KrLib7Mh_00569MemsetLib3cbzC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7mod_modC49OSSVerify5KrLib8PropExec<bv_wrap8_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib7Mh_00569MemsetLib5cbyteC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib7Mh_00569MemsetLib9cbyte_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLibAmod4_mod_pow2_genC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib7ms_replC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init9Datatypes7nat_indC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesc59OSSVerify5KrLib7Mh_00569MemsetLib>ms_repl_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7add_0_lC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c59OSSVerify5KrLib7Mh_00569MemsetLib9cbz_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib3c32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib4c32hC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib3c64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLibEZ_to_le_bytes_ms_replC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib9cbyte_cbzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib5u_c32C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc59OSSVerify5KrLib7Mh_00569MemsetLib5u_c64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z?mul_mod_distr_lC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulc59OSSVerify5KrLib7Mh_00569MemsetLib8u_slli56C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_mulhuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib6u_c32hC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z=testbit_neg_rC56Stdlib6ZArith6BinInt1Z;shiftl_specC49OSSVerify5KrLib8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorc59OSSVerify5KrLib7Mh_00569MemsetLibDlor_disjoint_shift32C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions?bv_half_modulusK46Stdlib9micromega7EnvRing5PExpr06C46Stdlib6ZArith4ZdivBZminus_mod_idemp_lc59OSSVerify5KrLib7Mh_00569MemsetLib>mod4_mod_pow2'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC49OSSVerify5KrLib8PropExec6v_subwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_modC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z:ones_equivC56Stdlib6ZArith6BinInt1Z=ones_mod_pow2C56Stdlib6ZArith8Zbitwise1Z?sub_land_same_lC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z:ldiff_landC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z<ldiff_ones_rC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z:land_assocc59OSSVerify5KrLib7Mh_00569MemsetLib;land_trunc4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbc59OSSVerify5KrLib7Mh_00569MemsetLib<land_4_casesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare5at_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib:ms_v_add_ZC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr0=K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC49OSSVerify5KrLib8PropExec9step_subwC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5instr0BC49OSSVerify5KrLib8PropExec:step_mulhuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop04K4ELinuxProcessSemantics5Riscv5Instr5instr0:C49OSSVerify5KrLib8PropExec7step_orC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5instr07C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib7Mh_00385Hoare7at_addiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib>cfill_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim:step_sb_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib;cfill_storeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize01C59OSSVerify5KrLib7Mh_00387SeqExec:step_sw_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03C59OSSVerify5KrLib7Mh_00387SeqExec:step_sd_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04C59OSSVerify5KrLib7Mh_00385Hoare?regs_agree_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib7ms_clobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare@regs_agree_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00569MemsetLib8ms_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare>regs_agree_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ms_inb (i : Z) (iv : Z * Z) : bool := (fst iv <=? i) && (i <? fst iv + snd iv).
Definition ms_cov (L : list (Z * Z)) (i : Z) : bool := existsb (ms_inb i) L.

Lemma ms_inb_true : forall i o m, ms_inb i (o, m) = true <-> o <= i < o + m.
Proof.
  intros i o m. unfold ms_inb. cbn [fst snd]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma ms_cov_cons : forall iv L i, ms_cov (iv :: L) i = ms_inb i iv || ms_cov L i.
Proof. reflexivity. Qed.

Lemma ms_cov_app : forall L1 L2 i, ms_cov (L1 ++ L2) i = ms_cov L1 i || ms_cov L2 i.
Proof. intros. unfold ms_cov. apply existsb_app. Qed.

Lemma ms_cov_In : forall L i o m, In (o, m) L -> o <= i < o + m -> ms_cov L i = true.
Proof.
  intros L i o m Hin Hi. unfold ms_cov. apply existsb_exists. exists (o, m). split; [exact Hin|].
  apply ms_inb_true. exact Hi.
Qed.

(* [comment removed for export] *)
Fixpoint ms_chain (from to : Z) (L : list (Z * Z)) : Prop :=
  match L with
  | [] => to <= from
  | (o, m) :: L' => o <= from /\ ms_chain (o + m) to L'
  end.

Lemma ms_chain_cov : forall L from to i,
  ms_chain from to L -> from <= i < to -> exists o m, In (o, m) L /\ o <= i < o + m.
Proof.
  induction L as [|[o m] L IH]; intros from to i Hc Hi; cbn [ms_chain] in Hc.
  - lia.
  - destruct Hc as [Ho Hc].
    destruct (Z.lt_ge_cases i (o + m)) as [Hlt|Hge].
    + exists o, m. split; [left; reflexivity | lia].
    + destruct (IH (o + m) to i Hc ltac:(lia)) as (o' & m' & Hin & Hi').
      exists o', m'. split; [right; exact Hin | exact Hi'].
Qed.

(* [comment removed for export] *)
Lemma ms_cov_by_chain : forall (L L' : list (Z * Z)) n,
  incl L' L -> ms_chain 0 n L' -> forall i, 0 <= i < n -> ms_cov L i = true.
Proof.
  intros L L' n Hincl Hc i Hi.
  destruct (ms_chain_cov L' 0 n i Hc Hi) as (o & m & Hin & Hom).
  apply (ms_cov_In L i o m); [apply Hincl, Hin | exact Hom].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CFill.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable c : byte.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.

  Definition cfill (L : list (Z * Z)) : word -> option byte :=
    fun x => if (bv_unsigned d <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned d + n)
                && ms_cov L (bv_unsigned x - bv_unsigned d)
             then Some c else mem0 x.

  Lemma cfill_nil : cfill [] = mem0.
  Proof.
    apply functional_extensionality. intro x. unfold cfill. cbn [ms_cov existsb].
    rewrite andb_false_r. reflexivity.
  Qed.

  Lemma cfill_grows : forall L, mem_grows mem0 (cfill L).
  Proof.
    intros L x Hx. unfold cfill. destruct (_ && _); [discriminate | exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_ext : forall L1 L2,
    (forall i, 0 <= i < n -> ms_cov L1 i = ms_cov L2 i) -> cfill L1 = cfill L2.
  Proof.
    intros L1 L2 H. apply functional_extensionality. intro x. unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|reflexivity].
    destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|reflexivity].
    cbn [andb]. rewrite H by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_store : forall L o (m : nat),
    0 <= o -> o + Z.of_nat m <= n ->
    wbytes (cfill L) (at_ d o) (repeat c m) = cfill ((o, Z.of_nat m) :: L).
  Proof.
    intros L o m Ho Hm. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    assert (Ha : bv_unsigned (at_ d o) = bv_unsigned d + o) by (apply at_u; lia).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o)) as [Hlo|Hge];
      [| destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o + Z.of_nat m)) as [Hin|Hhi]].
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
    - rewrite wbytes_inside by (rewrite repeat_length, Ha; lia).
      rewrite nth_repeat_lt by (rewrite Ha; lia). unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with true
        by (symmetry; apply ms_inb_true; lia).
      destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|lia].
      destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|lia].
      reflexivity.
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_full : forall L,
    (forall i, 0 <= i < n -> ms_cov L i = true) ->
    cfill L = wbytes mem0 d (repeat c (Z.to_nat n)).
  Proof.
    intros L Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)) as [H1|H1].
    - destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)) as [H2|H2]; cbn [andb].
      + rewrite Hcov by lia. rewrite wbytes_inside by (rewrite repeat_length; lia).
        rewrite nth_repeat_lt by lia. reflexivity.
      + rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
    - cbn [andb]. rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
  Qed.

  Lemma cfill_full_chain : forall L L',
    incl L' L -> ms_chain 0 n L' ->
    cfill L = wbytes mem0 d (repeat c (Z.to_nat n)).
  Proof. intros L L' Hi Hc. apply cfill_full. apply (ms_cov_by_chain L L'); assumption. Qed.

  (* [comment removed for export] *)
  Lemma cfill_store_ok : forall segs L o (m : nat),
    store_ok segs mem0 d (Z.to_nat n) = true ->
    0 <= o -> o + Z.of_nat m <= n ->
    store_ok segs (cfill L) (at_ d o) m = true.
  Proof.
    intros segs L o m Hok Ho Hm. pose proof (u64_range d).
    apply (store_ok_mono segs m mem0); [apply cfill_grows|].
    apply (store_ok_sub segs mem0 d (at_ d o) (Z.to_nat n) m); try (rewrite ?at_u; lia). exact Hok.
  Qed.
End CFill.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod4_mod_pow2_gen : forall t k j, 0 <= j <= k -> (t mod 2 ^ k) mod 2 ^ j = t mod 2 ^ j.
Proof.
  intros t k j Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - j)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition cbyte (cv : word) : byte := Z_to_bv 8 (bv_unsigned cv).
(* [comment removed for export] *)
Definition cbz (cv : word) : Z := bv_unsigned cv mod 256.
(* [comment removed for export] *)
Definition c32 (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009).
(* [comment removed for export] *)
Definition c32h (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009 * 2 ^ 32).
(* [comment removed for export] *)
Definition c64 (cv : word) : word := Z_to_bv 64 (cbz cv * 72340172838076673).

Lemma cbz_range : forall cv, 0 <= cbz cv < 256.
Proof. intros cv. unfold cbz. apply Z.mod_pos_bound. lia. Qed.

Lemma cbyte_mod : forall cv, Z_to_bv 8 (bv_unsigned cv mod 256) = cbyte cv.
Proof.
  intros cv. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. apply Z.mod_mod. lia.
Qed.

Lemma cbyte_cbz : forall cv, cbyte cv = Z_to_bv 8 (cbz cv).
Proof. intros cv. unfold cbz. symmetry. apply cbyte_mod. Qed.

(* [comment removed for export] *)
Lemma cbyte_Z : forall z, cbyte (Z_to_bv 64 z) = Z_to_bv 8 z.
Proof.
  intros z. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod, bv_wrap64_mod.
  apply mod4_mod_pow2_gen. lia.
Qed.

(* [comment removed for export] *)
Fixpoint ms_repl (k : nat) : Z := match k with O => 0 | S k' => 1 + 256 * ms_repl k' end.

Lemma ms_repl_nonneg : forall k, 0 <= ms_repl k.
Proof. induction k; cbn [ms_repl]; lia. Qed.

Lemma Z_to_le_bytes_ms_repl : forall k z, 0 <= z < 256 ->
  Z_to_le_bytes k (z * ms_repl k) = repeat (Z_to_bv 8 z) k.
Proof.
  induction k as [|k IH]; intros z Hz; [reflexivity|].
  cbn [Z_to_le_bytes ms_repl repeat]. pose proof (ms_repl_nonneg k). f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply IH. exact Hz.
Qed.

Lemma u_c32 : forall cv, bv_unsigned (c32 cv) = cbz cv * 16843009.
Proof. intros cv. pose proof (cbz_range cv). unfold c32. apply u_Z2bv; lia. Qed.

Lemma u_c32h : forall cv, bv_unsigned (c32h cv) = cbz cv * 16843009 * 2 ^ 32.
Proof. intros cv. pose proof (cbz_range cv). unfold c32h. apply u_Z2bv; lia. Qed.

Lemma u_c64 : forall cv, bv_unsigned (c64 cv) = cbz cv * 72340172838076673.
Proof. intros cv. pose proof (cbz_range cv). unfold c64. apply u_Z2bv; lia. Qed.

Lemma wleb4_c32 : forall cv, word_to_le_bytes 4 (c32 cv) = repeat (cbyte cv) 4.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c32, cbyte_cbz.
  change 16843009 with (ms_repl 4). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

Lemma wleb8_c64 : forall cv, word_to_le_bytes 8 (c64 cv) = repeat (cbyte cv) 8.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c64, cbyte_cbz.
  change 72340172838076673 with (ms_repl 8). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

(* [comment removed for export] *)
Lemma u_slli56 : forall cv, bv_unsigned (v_slli cv 56) = cbz cv * 2 ^ 56.
Proof.
  intros cv. unfold v_slli, cbz. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia.
  pose proof (u64_range cv).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 56 * 256).
  rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mulhu_c32 : forall cv (m : word), bv_unsigned m = 4311810304 ->
  v_mulhu (v_slli cv 56) m = c32 cv.
Proof.
  intros cv m Hm. unfold v_mulhu, c32. f_equal. rewrite u_slli56, Hm.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (cbz cv * 2 ^ 56 * 4311810304) with ((cbz cv * 16843009) * 2 ^ 64) by lia.
  apply Z.div_mul. lia.
Qed.

Lemma slli32_c32 : forall cv, v_slli (c32 cv) 32 = c32h cv.
Proof.
  intros cv. unfold v_slli, c32h. f_equal. rewrite u_c32, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma srli32_c32h : forall cv, v_srli (c32h cv) 32 = c32 cv.
Proof.
  intros cv. unfold v_srli, c32. f_equal. rewrite u_c32h, Z.shiftr_div_pow2 by lia.
  apply Z.div_mul. lia.
Qed.

Lemma lor_disjoint_shift32 : forall a b, 0 <= a -> 0 <= b < 2 ^ 32 ->
  Z.lor (a * 2 ^ 32) b = a * 2 ^ 32 + b.
Proof.
  intros a b Ha Hb.
  assert (Hl : Z.land (a * 2 ^ 32) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32).
    - rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r a) by lia. reflexivity.
    - rewrite (Z_testbit_high 32 b) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.

Lemma or_c64 : forall cv, v_or (c32h cv) (c32 cv) = c64 cv.
Proof.
  intros cv. pose proof (cbz_range cv). unfold v_or, c64. f_equal. rewrite u_c32h, u_c32.
  rewrite lor_disjoint_shift32 by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod4_mod_pow2' : forall t k, 2 <= k -> (t mod 2 ^ k) mod 4 = t mod 4.
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - 2)). change 4 with (2 ^ 2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3 : forall x : word,
  v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 ((- bv_unsigned x) mod 4).
Proof.
  intros x. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2 ^ 31).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (2 ^ 2) with 4.
  rewrite mod4_mod_pow2' by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2' by lia.
  replace (0 - bv_unsigned x + 2 ^ 31) with ((- bv_unsigned x) + 536870912 * 4) by lia.
  rewrite Z.mod_add by lia.
  rewrite Zminus_mod_idemp_l.
  replace (- bv_unsigned x - 2 ^ 31) with ((- bv_unsigned x) + (- 536870912) * 4) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma neg_mod4_range : forall u, 0 <= (- u) mod 4 <= 3.
Proof. intros u. pose proof (Z.mod_pos_bound (- u) 4). lia. Qed.

Lemma neg_mod4_aligns : forall u, (u + (- u) mod 4) mod 4 = 0.
Proof.
  intros u. rewrite Z.add_mod, Z.mod_mod by lia.
  rewrite <- Z.add_mod by lia. replace (u + - u) with 0 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_trunc4 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 4) = a - a mod 4.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 4) with (Z.ldiff (Z.ones 64) (Z.ones 2)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  pose proof (Z.div_mod a 4 ltac:(lia)). lia.
Qed.

Lemma andi_m4 : forall m, 0 <= m < 2 ^ 64 ->
  v_andi (Z_to_bv 64 m) (-4) = Z_to_bv 64 (m - m mod 4).
Proof.
  intros m Hm. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
  change (bv_wrap 64 (-4)) with (2 ^ 64 - 4). apply land_trunc4. exact Hm.
Qed.

(* [comment removed for export] *)
Lemma land_4_cases : forall a, 0 <= a -> Z.land a 4 = 0 \/ Z.land a 4 = 4.
Proof.
  intros a Ha.
  destruct (Z.testbit a 2) eqn:E; [right|left];
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec;
    change 4 with (2 ^ 2); rewrite Z.pow2_bits_eqb by lia;
    destruct (Z.eqb_spec 2 i) as [<-|Hne]; rewrite ?E, ?Z.bits_0; try reflexivity;
    apply andb_false_r.
Qed.

Lemma andi_4_cases : forall x : word, exists s4, v_andi x 4 = Z_to_bv 64 s4 /\ (s4 = 0 \/ s4 = 4).
Proof.
  intros x. exists (Z.land (bv_unsigned x) 4). split.
  - unfold v_andi. f_equal.
  - apply land_4_cases. apply u64_range.
Qed.

(* [comment removed for export] *)
Lemma ms_v_add_Z : forall (x : word) z, 0 <= z < 2 ^ 64 ->
  v_add x (Z_to_bv 64 z) = at_ x z.
Proof. intros x z Hz. unfold v_add, at_. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_add_at_Z : forall (x : word) o z, 0 <= z < 2 ^ 64 ->
  v_add (at_ x o) (Z_to_bv 64 z) = at_ x (o + z).
Proof. intros x o z Hz. rewrite ms_v_add_Z by lia. apply at_at. Qed.

Lemma ms_v_sub_ZZ : forall a b, 0 <= b <= a -> a < 2 ^ 64 ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H1 H2. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_addi_Z : forall a i, 0 <= a < 2 ^ 64 ->
  v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha. unfold v_addi. rewrite u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ms_step_subw_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_subw (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_mulhu_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULHU rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_mulhu (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mulhu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stores.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable cv : word.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.
  Hypothesis Hok : store_ok segs mem0 d (Z.to_nat n) = true.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).

  Lemma cf_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = cv ->
    0 <= o -> o + 1 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 1) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o Hf He Hdc Hrs1 Ho Hrs2 H0 H1.
    replace ((o, 1) :: L) with ((o, Z.of_nat 1) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 1) by lia.
    eapply step_sb_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 | reflexivity |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sw : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o v,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 4 v = repeat (cbyte cv) 4 ->
    0 <= o -> o + 4 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 4) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 4) :: L) with ((o, Z.of_nat 4) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 4) by lia.
    rewrite <- Hv.
    eapply step_sw_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sd : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o v,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 8 v = repeat (cbyte cv) 8 ->
    0 <= o -> o + 8 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 8) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 8) :: L) with ((o, Z.of_nat 8) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 8) by lia.
    rewrite <- Hv.
    eapply step_sd_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.
End Stores.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ms_clob : list reg := [11; 12; 13; 14; 15; 16]%bv.
Definition ms_agree (regs regs' : bvmap 5 word) : Prop :=
  regs_agree (fun r => In r ms_clob) regs regs'.

Lemma ms_agree_refl : forall regs, ms_agree regs regs.
Proof. intros regs. apply regs_agree_refl. Qed.

Lemma ms_agree_trans : forall r1 r2 r3, ms_agree r1 r2 -> ms_agree r2 r3 -> ms_agree r1 r3.
Proof. intros r1 r2 r3. apply regs_agree_trans. Qed.

Lemma ms_agree_upd : forall regs regs' (rd : reg) v,
  ms_agree regs regs' -> In rd ms_clob -> ms_agree regs (regupd regs' rd v).
Proof. intros regs regs' rd v H Hin. apply regs_agree_upd; assumption. Qed.

Lemma ms_agree_getr : forall regs regs' (r : reg),
  ms_agree regs regs' -> ~ In r ms_clob -> getr regs' r = getr regs r.
Proof. intros regs regs' r H Hn. apply H. exact Hn. Qed.

Lemma ms_agree_keeps : forall regs regs', ms_agree regs regs' -> keeps regs regs'.
Proof.
  intros regs regs' H r Hr. apply H. unfold callee_kept in Hr. unfold ms_clob. cbn [In] in *.
  intros Hc. decompose [or] Hr; subst; decompose [or] Hc; try discriminate; auto.
Qed.
End FPX_1.


Ltac in_clob := cbn [ms_clob In]; repeat first [ left; reflexivity | right ].
Ltac solve_ms_agree :=
  repeat (apply ms_agree_upd; [| in_clob]); first [apply ms_agree_refl | assumption].

End MemsetLib.
From Stdlib Require NArith ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Module MuslStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_MuslStrlen () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib3subC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib:firstn_addC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib>firstn_sub_appC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9skipn_addC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib:sub_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9sub_splitC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9sub_0_allC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056<RefMemcpyLib@length_firstn_idC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ2zbC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4Zdiv8Zdiv_0_lC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z4lxorC47Corelib4Init9Datatypes4xorbC56Stdlib6ZArith6BinInt1Z9lxor_specC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z;lxor_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula09C56Stdlib6ZArith6BinInt1Z4onesK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z9land_onesc69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ;land_lxor_mC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init5Logic3and01I47Corelib4Init5Logic4True00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ;land_land_mC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;shiftr_landc69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ6zb_altC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;shiftr_lxorc69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ4zdigC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List?Forall_cons_iffK46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init9Datatypes8list_indI46Stdlib5Lists4List6Exists00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z9pow_add_rC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums1N01K46Stdlib9micromega=RingMicromega3Op201C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula03c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ;zdig_nonnegC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z7div_1_rC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z9div_add_lC56Stdlib6ZArith6BinInt1Z7div_divC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI47Corelib4Init5Logic5False00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ;zdig_recon8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ4zb_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ;pow2_8i_posC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z8mul_commC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z?divide_factor_lC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06I47Corelib4Init5Logic2ex00C56Stdlib6ZArith8Zbitwise1Z?sub_land_same_lC56Stdlib6ZArith6BinInt1Z4lnotI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z;land_nonnegK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z9land_commc69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ9land_le_rC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ2TzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ7ONESNEGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ7ALLONESC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ5HIGHSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ8zb_HIGHSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ:zb_ALLONESC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ7zb_lxorC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ7zb_landC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List2InI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib5Lists4List7forallbC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6eqb_eqK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ8zb_boundC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ7zdig_ltC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityc69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ8Tz_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ;byte_nozeroC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ7zb_zdigC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ7Tz_byteC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ6zb_eq0C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2Zrc69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ8zb_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ<zb_split_255C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ<sum_byte_255C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ8zb_mod64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ7zb_neq0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1ZAmul_pow2_bits_lowC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z=testbit_falseC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorI45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC47Corelib5Lists7ListDef3mapC49OSSVerify5KrLib8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_mapC46Stdlib5Lists4List=Forall_forallc59OSSVerify5KrLib7Mh_0056:MuslStrlen;lor_shiftl8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_nthC46Stdlib5Lists4List:length_mapc59OSSVerify5KrLib7Mh_0056:MuslStrlenBbytes_le_to_Z_zdigC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056:MuslStrlen7u8_zeroC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapc69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ9lxor_lt64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0056:MuslStrlen2HZ9land_le_lC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8firstn_0C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC49OSSVerify5KrLib8PropExecCtotal_arg_bytes_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecDtotal_arg_bytes_consC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List:length_appI47Corelib4Init9Datatypes4prod00C47Corelib4Init3Nat3mulC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout=at_random_ptrC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout:auxv_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<string_addrsC47Corelib4Init9Datatypes3fstK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutFlength_at_random_bytesC49OSSVerify5KrLib8PropExecFlength_flatten_stringsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAlength_auxv_bytesC49OSSVerify5KrLib8PropExec@length_n_to_le_8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecGlength_string_addrs_fstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecClength_flat_map_le8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecAstring_addrs_pairC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec?cat_struct_sizeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC46Stdlib5Lists4List8flat_mapC47Corelib5Lists7ListDef6repeatC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9auxv_sizeI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C46Stdlib5Lists4List<firstn_skipnC59OSSVerify5KrLib7Mh_00387CatExec:bsb_byte_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056:MuslStrlen=bsb_len_lowerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecItotal_arg_bytes_firstn_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056:MuslStrlenHtotal_arg_bytes_firstn_SC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List@firstn_length_leC47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnK47Corelib4Init5Logic2ex01C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxc59OSSVerify5KrLib7Mh_0056:MuslStrlen:bsb_word_kC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib7Mh_00387CatExec?cat_string_baseC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecEnat_to_word_add_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCcat_argv_ptr_offsetC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecDread_at_offset_imageC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib7Mh_00387CatExec7byte_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec7rdn_nthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib7Mh_00387StepTac9bsb_boundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056:MuslStrlen:mstr_sp_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac<word_add_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056:MuslStrlen:mstr_sp_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056:MuslStrlen;mstr_bsb_nwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec?argv_ptr_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExecAargv_layout_slackC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056:MuslStrlenDmstr_argv_ptr_boundsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056:MuslStrlen=argv_ptr_roomC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0056:MuslStrlen?read_word_stackC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecDrdn_wrap_stack_aboveC1?~~~~~~~~~~~~~~~".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module HZ.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition zb (x : Z) (i : nat) : Z := (x / 2^(8 * Z.of_nat i)) mod 256.

Fixpoint zdig (ds : list Z) : Z :=
  match ds with [] => 0 | d :: r => d + 256 * zdig r end.

Lemma pow2_8i_pos : forall i : nat, 0 < 2^(8 * Z.of_nat i).
Proof. intro i. apply Z.pow_pos_nonneg; lia. Qed.

Lemma zb_bound : forall x i, 0 <= zb x i < 256.
Proof. intros. unfold zb. apply Z.mod_pos_bound. lia. Qed.

Lemma zb_0 : forall i, zb 0 i = 0.
Proof. intro i. unfold zb. rewrite Zdiv_0_l. reflexivity. Qed.

(* [comment removed for export] *)

Lemma land_land_m : forall a b m, Z.land (Z.land a b) m = Z.land (Z.land a m) (Z.land b m).
Proof.
  intros. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.

Lemma land_lxor_m : forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof.
  intros. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.

Lemma lxor_lt64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  0 <= Z.lxor a b < 2^64.
Proof.
  intros a b Ha Hb.
  assert (Hn : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [lia|].
  assert (E : Z.lxor a b mod 2^64 = Z.lxor a b).
  { rewrite <- Z.land_ones by lia. rewrite land_lxor_m.
    rewrite !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
  rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.

Lemma zb_alt : forall x i, zb x i = Z.land (Z.shiftr x (8 * Z.of_nat i)) 255.
Proof.
  intros x i. unfold zb.
  rewrite Z.shiftr_div_pow2 by lia.
  change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma zb_land : forall u w i, zb (Z.land u w) i = Z.land (zb u i) (zb w i).
Proof.
  intros u w i. rewrite !zb_alt.
  rewrite Z.shiftr_land, land_land_m. reflexivity.
Qed.

Lemma zb_lxor : forall u w i, zb (Z.lxor u w) i = Z.lxor (zb u i) (zb w i).
Proof.
  intros u w i. rewrite !zb_alt.
  rewrite Z.shiftr_lxor, land_lxor_m. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma zdig_nonneg : forall ds, Forall (fun d => 0 <= d < 256) ds -> 0 <= zdig ds.
Proof.
  induction ds as [|d ds IH]; intro H; cbn [zdig]; [lia|].
  apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
  specialize (IH Hds). lia.
Qed.

Lemma zdig_lt : forall ds, Forall (fun d => 0 <= d < 256) ds ->
  zdig ds < 2^(8 * Z.of_nat (length ds)).
Proof.
  induction ds as [|d ds IH]; intro H; cbn [zdig length].
  - cbn. lia.
  - apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
    specialize (IH Hds).
    replace (8 * Z.of_nat (S (length ds))) with (8 + 8 * Z.of_nat (length ds)) by lia.
    rewrite Z.pow_add_r by lia. change (2^8) with 256. lia.
Qed.

Lemma zb_zdig : forall ds, Forall (fun d => 0 <= d < 256) ds ->
  forall i, (i < length ds)%nat -> zb (zdig ds) i = nth i ds 0.
Proof.
  induction ds as [|d ds IH]; intros H i Hi; [cbn in Hi; lia|].
  apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
  pose proof (zdig_nonneg ds Hds) as Hnn.
  destruct i as [|i]; cbn [nth].
  - cbn [zdig]. unfold zb.
    change (8 * Z.of_nat 0) with 0. change (2^0) with 1.
    rewrite Z.div_1_r.
    replace (d + 256 * zdig ds) with (d + zdig ds * 256) by lia.
    rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
  - cbn [length] in Hi.
    rewrite <- (IH Hds i ltac:(lia)).
    cbn [zdig]. unfold zb.
    replace (8 * Z.of_nat (S i)) with (8 + 8 * Z.of_nat i) by lia.
    rewrite Z.pow_add_r by lia. change (2^8) with 256.
    rewrite <- Z.div_div by (try lia; apply pow2_8i_pos).
    replace ((d + 256 * zdig ds) / 256) with (zdig ds); [reflexivity|].
    replace (d + 256 * zdig ds) with (zdig ds * 256 + d) by lia.
    rewrite Z.div_add_l by lia.
    rewrite (Z.div_small d 256) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma zdig_recon8 : forall x, 0 <= x < 2^64 ->
  x = zdig [zb x 0; zb x 1; zb x 2; zb x 3; zb x 4; zb x 5; zb x 6; zb x 7].
Proof.
  intros x Hx. cbn [zdig]. unfold zb.
  change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8.
  change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
  change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 5) with 40.
  change (8 * Z.of_nat 6) with 48. change (8 * Z.of_nat 7) with 56.
  change (2^0) with 1. rewrite Z.div_1_r.
  change (2^8) with 256.
  change (2^16) with (256*256).
  change (2^24) with (256*256*256).
  change (2^32) with (256*256*256*256).
  change (2^40) with (256*256*256*256*256).
  change (2^48) with (256*256*256*256*256*256).
  change (2^56) with (256*256*256*256*256*256*256).
  rewrite <- !Z.div_div by lia.
  pose proof (Z.div_mod x 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256/256/256/256) 256 ltac:(lia)).
  assert (Htop : x/256/256/256/256/256/256/256/256 = 0).
  { rewrite !Z.div_div by lia. apply Z.div_small. lia. }
  lia.
Qed.

Lemma zb_eq0 : forall x, 0 <= x < 2^64 ->
  (forall i, (i < 8)%nat -> zb x i = 0) -> x = 0.
Proof.
  intros x Hx H. rewrite (zdig_recon8 x Hx).
  rewrite !H by lia. cbn [zdig]. lia.
Qed.

Lemma zb_neq0 : forall x i, zb x i <> 0 -> x <> 0.
Proof. intros x i H Hc. subst. rewrite zb_0 in H. lia. Qed.

(* [comment removed for export] *)

Lemma zb_split : forall lo hi i,
  0 <= lo < 2^(8 * Z.of_nat i) -> 0 <= hi ->
  zb (lo + 2^(8 * Z.of_nat i) * hi) i = hi mod 256.
Proof.
  intros lo hi i Hlo Hhi. unfold zb.
  rewrite Z.mul_comm, Z.div_add by (pose proof (pow2_8i_pos i); lia).
  rewrite (Z.div_small lo) by lia. reflexivity.
Qed.

Lemma zb_mod64 : forall y i, (i < 8)%nat -> 0 <= y < 2^65 ->
  zb (y mod 2^64) i = zb y i.
Proof.
  intros y i Hi Hy.
  destruct (Z_lt_le_dec y (2^64)) as [Hlt|Hge].
  - rewrite Z.mod_small by lia. reflexivity.
  - assert (Hm : y mod 2^64 = y - 2^64).
    { replace y with ((y - 2^64) + 1 * 2^64) at 1 by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite Hm. unfold zb.
    pose proof (pow2_8i_pos i) as Hk.
    assert (Hd : 2^64 = 2^(64 - 8 * Z.of_nat i) * 2^(8 * Z.of_nat i)).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Hdiv : (256 | 2^(64 - 8 * Z.of_nat i))).
    { replace (64 - 8 * Z.of_nat i) with (8 + (56 - 8 * Z.of_nat i)) by lia.
      rewrite Z.pow_add_r by lia. change (2^8) with 256.
      apply Z.divide_factor_l. }
    destruct Hdiv as [q Hq].
    replace (y - 2^64) with (y + (- (q * 256)) * 2^(8 * Z.of_nat i))
      by (rewrite Hd, Hq; lia).
    rewrite Z.div_add by lia.
    replace (y / 2 ^ (8 * Z.of_nat i) + - (q * 256))
      with (y / 2 ^ (8 * Z.of_nat i) + (- q) * 256) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)

Definition ONESNEG : Z := 18374403900871474943.   (* [comment removed for export] *)
Definition HIGHS   : Z := 9259542123273814144.    (* [comment removed for export] *)
Definition ALLONES : Z := 18446744073709551615.   (* [comment removed for export] *)

Definition Tz (x : Z) : Z :=
  Z.land (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS.

Lemma land_le_r : forall a b, 0 <= b -> Z.land a b <= b.
Proof.
  intros a b Hb.
  rewrite Z.land_comm.
  pose proof (Z.sub_land_same_l b a) as H.
  assert (0 <= Z.land b (Z.lnot a)) by (apply Z.land_nonneg; left; lia).
  lia.
Qed.

Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof. intros a b Ha. rewrite Z.land_comm. apply land_le_r. exact Ha. Qed.

Lemma Tz_range : forall x, 0 <= Tz x < 2^64.
Proof.
  intro x. unfold Tz. split.
  - apply Z.land_nonneg. right. unfold HIGHS. lia.
  - pose proof (land_le_r (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS
                  ltac:(unfold HIGHS; lia)). unfold HIGHS in *. lia.
Qed.

Ltac by8 i := destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia; vm_compute; reflexivity.

Lemma zb_ALLONES : forall i, (i < 8)%nat -> zb ALLONES i = 255.
Proof. intros i Hi. by8 i. Qed.

Lemma zb_HIGHS : forall i, (i < 8)%nat -> zb HIGHS i = 128.
Proof. intros i Hi. by8 i. Qed.

Lemma Tz_byte : forall x i, (i < 8)%nat ->
  zb (Tz x) i
  = Z.land (Z.land (zb ((x + ONESNEG) mod 2^64) i) (Z.lxor (zb x i) 255)) 128.
Proof.
  intros x i Hi. unfold Tz.
  rewrite !zb_land, zb_lxor, zb_ALLONES by exact Hi.
  rewrite zb_HIGHS by exact Hi. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma byte_nozero : forall c, 1 <= c <= 255 ->
  Z.land (Z.land (c - 1) (Z.lxor c 255)) 128 = 0.
Proof.
  intros c Hc.
  assert (Hin : In (Z.to_nat c) (seq 1 255)) by (apply in_seq; lia).
  assert (Hall : forallb (fun n =>
      Z.eqb (Z.land (Z.land (Z.of_nat n - 1) (Z.lxor (Z.of_nat n) 255)) 128) 0)
      (seq 1 255) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall _ Hin).
  apply Z.eqb_eq in Hall.
  replace (Z.of_nat (Z.to_nat c)) with c in Hall by lia. exact Hall.
Qed.

(* [comment removed for export] *)
Lemma Tz_nozero : forall x, 0 <= x < 2^64 ->
  (forall i, (i < 8)%nat -> zb x i <> 0) -> Tz x = 0.
Proof.
  intros x Hx Hnz.
  pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
  pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
  pose proof (zb_bound x 6). pose proof (zb_bound x 7).
  pose proof (Hnz 0%nat ltac:(lia)). pose proof (Hnz 1%nat ltac:(lia)).
  pose proof (Hnz 2%nat ltac:(lia)). pose proof (Hnz 3%nat ltac:(lia)).
  pose proof (Hnz 4%nat ltac:(lia)). pose proof (Hnz 5%nat ltac:(lia)).
  pose proof (Hnz 6%nat ltac:(lia)). pose proof (Hnz 7%nat ltac:(lia)).
  pose proof (zdig_recon8 x Hx) as Hrec.
  set (ds' := [zb x 0 - 1; zb x 1 - 1; zb x 2 - 1; zb x 3 - 1;
               zb x 4 - 1; zb x 5 - 1; zb x 6 - 1; zb x 7 - 1]).
  assert (Hds' : Forall (fun d => 0 <= d < 256) ds').
  { unfold ds'. repeat constructor; lia. }
  assert (Hlt' : 0 <= zdig ds' < 2^64).
  { split; [apply zdig_nonneg; exact Hds'|].
    pose proof (zdig_lt ds' Hds') as H'. unfold ds' in H' |- *.
    cbn [length] in H'. exact H'. }
  assert (Hy : (x + ONESNEG) mod 2^64 = zdig ds').
  { rewrite Hrec at 1.
    replace (zdig [zb x 0; zb x 1; zb x 2; zb x 3; zb x 4; zb x 5; zb x 6; zb x 7]
             + ONESNEG)
      with (zdig ds' + 1 * 2^64)
      by (unfold ds', ONESNEG; cbn [zdig]; lia).
    rewrite Z.mod_add by lia. apply Z.mod_small. exact Hlt'. }
  apply zb_eq0; [apply Tz_range|].
  intros i Hi. rewrite Tz_byte by exact Hi. rewrite Hy.
  rewrite (zb_zdig ds' Hds' i) by (unfold ds'; cbn [length]; lia).
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia;
    unfold ds'; cbn [nth]; apply byte_nozero; lia.
Qed.

Lemma zb_split_255 : forall v lo Q i p,
  p = 2^(8 * Z.of_nat i) -> v = lo + p * (255 + 256 * Q) ->
  0 <= lo < p -> 0 <= Q -> zb v i = 255.
Proof.
  intros v lo Q i p Hp Hv Hlo HQ. subst p v.
  rewrite zb_split by (try lia; assumption).
  replace (255 + 256 * Q) with (255 + Q * 256) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma sum_byte_255 : forall x i, 0 <= x < 2^64 -> (i < 8)%nat -> zb x i = 0 ->
  (forall j, (j < i)%nat -> zb x j <> 0) ->
  zb (x + ONESNEG) i = 255.
Proof.
  intros x i Hx Hi Hz Hlow.
  pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
  pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
  pose proof (zb_bound x 6). pose proof (zb_bound x 7).
  pose proof (zdig_recon8 x Hx) as Hrec. cbn [zdig] in Hrec.
  unfold ONESNEG.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia.
  - (* byte 0 *)
    apply (zb_split_255 _ (0) (zb x 1 * 1 + zb x 2 * 256 + zb x 3 * 65536 + zb x 4 * 16777216 + zb x 5 * 4294967296 + zb x 6 * 1099511627776 + zb x 7 * 281474976710656 + 71775015237779198) 0%nat 1);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* byte 1 *)
    pose proof (Hlow 0%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1) (zb x 2 * 1 + zb x 3 * 256 + zb x 4 * 65536 + zb x 5 * 16777216 + zb x 6 * 4294967296 + zb x 7 * 1099511627776 + 280371153272574) 1%nat 256);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* byte 2 *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256) (zb x 3 * 1 + zb x 4 * 256 + zb x 5 * 65536 + zb x 6 * 16777216 + zb x 7 * 4294967296 + 1095199817470) 2%nat 65536);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* byte 3 *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536) (zb x 4 * 1 + zb x 5 * 256 + zb x 6 * 65536 + zb x 7 * 16777216 + 4278124286) 3%nat 16777216);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* byte 4 *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216) (zb x 5 * 1 + zb x 6 * 256 + zb x 7 * 65536 + 16711422) 4%nat 4294967296);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* byte 5 *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    pose proof (Hlow 4%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296) (zb x 6 * 1 + zb x 7 * 256 + 65278) 5%nat 1099511627776);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* byte 6 *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    pose proof (Hlow 4%nat ltac:(lia)).
    pose proof (Hlow 5%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776) (zb x 7 * 1 + 254) 6%nat 281474976710656);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* byte 7 *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    pose proof (Hlow 4%nat ltac:(lia)).
    pose proof (Hlow 5%nat ltac:(lia)).
    pose proof (Hlow 6%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776 + (zb x 6 - 1) * 281474976710656) (0) 7%nat 72057594037927936);
      [ vm_compute; reflexivity | lia | lia | lia ].
Qed.

(* [comment removed for export] *)
Lemma Tz_haszero : forall x i, 0 <= x < 2^64 -> (i < 8)%nat -> zb x i = 0 ->
  (forall j, (j < i)%nat -> zb x j <> 0) -> Tz x <> 0.
Proof.
  intros x i Hx Hi Hz Hlow.
  apply (zb_neq0 _ i).
  rewrite Tz_byte by exact Hi.
  rewrite zb_mod64 by (first [exact Hi | unfold ONESNEG; lia]).
  rewrite (sum_byte_255 x i Hx Hi Hz Hlow), Hz.
  vm_compute. discriminate.
Qed.

End HZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u8_zero : bv_unsigned (Z_to_bv 8 0) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma lor_shiftl8 : forall a y : Z, (0 <= a < 256)%Z -> (0 <= y)%Z ->
  Z.lor a (Z.shiftl y 8) = (a + 256 * y)%Z.
Proof.
  intros a y Ha Hy.
  assert (Hs : Z.shiftl y 8 = (y * 2^8)%Z) by (apply Z.shiftl_mul_pow2; lia).
  assert (Hland : Z.land a (Z.shiftl y 8) = 0%Z).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb n 8) eqn:E.
    - apply Z.ltb_lt in E.
      rewrite Hs, Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - apply Z.ltb_ge in E.
      replace (Z.testbit a n) with false; [reflexivity|].
      symmetry. apply Z.testbit_false; [lia|].
      rewrite Z.div_small; [reflexivity|].
      split; [lia|]. eapply Z.lt_le_trans; [apply Ha|].
      change 256%Z with (2^8)%Z. apply Z.pow_le_mono_r; lia. }
  rewrite <- Z.lxor_lor by exact Hland.
  rewrite <- Z.add_nocarry_lxor by exact Hland.
  rewrite Hs. lia.
Qed.

Lemma bytes_le_to_Z_zdig : forall bs : list byte,
  bytes_le_to_Z bs = HZ.zdig (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [bytes_le_to_Z map HZ.zdig]. rewrite IH.
  apply lor_shiftl8; [apply u8_range|].
  apply HZ.zdig_nonneg. apply Forall_map, Forall_forall.
  intros x _. apply u8_range.
Qed.

Lemma zb_of_bytes : forall (bs : list byte) i, (i < length bs)%nat ->
  HZ.zb (bytes_le_to_Z bs) i = bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof.
  intros bs i Hi. rewrite bytes_le_to_Z_zdig.
  rewrite HZ.zb_zdig
    by (first [ apply Forall_map, Forall_forall; intros x _; apply u8_range
              | rewrite length_map; exact Hi ]).
  rewrite <- (map_nth bv_unsigned bs (Z_to_bv 8 0) i), u8_zero. reflexivity.
Qed.

Lemma bytes_le_to_Z_range : forall bs : list byte, length bs = 8%nat ->
  (0 <= bytes_le_to_Z bs < 2^64)%Z.
Proof.
  intros bs Hl. rewrite bytes_le_to_Z_zdig.
  assert (HF : Forall (fun d => (0 <= d < 256)%Z) (map bv_unsigned bs))
    by (apply Forall_map, Forall_forall; intros x _; apply u8_range).
  split; [apply HZ.zdig_nonneg; exact HF|].
  pose proof (HZ.zdig_lt _ HF) as H.
  rewrite length_map, Hl in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma v_haszero : forall v : word,
  bv_unsigned
    (v_and (v_and (v_add v (Z_to_bv 64 18374403900871474943))
                  (v_xori v (-1)))
           (Z_to_bv 64 9259542123273814144))
  = HZ.Tz (bv_unsigned v).
Proof.
  intro v. pose proof (u64_range v) as Hv.
  unfold v_and, v_add, v_xori, HZ.Tz, HZ.ONESNEG, HZ.HIGHS, HZ.ALLONES.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small 18374403900871474943 (2^64)) by lia.
  rewrite (Z.mod_small 9259542123273814144 (2^64)) by lia.
  replace ((-1) mod 2^64)%Z with 18446744073709551615%Z
    by (vm_compute; reflexivity).
  assert (Hx : (0 <= Z.lxor (bv_unsigned v) 18446744073709551615 < 2^64)%Z)
    by (apply HZ.lxor_lt64; lia).
  rewrite (Z.mod_small (Z.lxor (bv_unsigned v) 18446744073709551615)) by exact Hx.
  assert (Hm : (0 <= (bv_unsigned v + 18374403900871474943) mod 2^64 < 2^64)%Z)
    by (apply Z.mod_pos_bound; lia).
  assert (Hz : (0 <= Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
                      (Z.lxor (bv_unsigned v) 18446744073709551615) < 2^64)%Z).
  { split; [apply Z.land_nonneg; left; lia|].
    pose proof (HZ.land_le_l ((bv_unsigned v + 18374403900871474943) mod 2^64)
                  (Z.lxor (bv_unsigned v) 18446744073709551615) ltac:(lia)). lia. }
  rewrite (Z.mod_small
    (Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
            (Z.lxor (bv_unsigned v) 18446744073709551615))
    (2^64)) by exact Hz.
  apply Z.mod_small. split.
  - apply Z.land_nonneg. right. lia.
  - pose proof (HZ.land_le_r
      (Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
              (Z.lxor (bv_unsigned v) 18446744073709551615))
      9259542123273814144 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma total_arg_bytes_firstn_S : forall (l : list (list byte)) k,
  (k < length l)%nat ->
  total_arg_bytes_nat (firstn (S k) l)
  = (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1)%nat.
Proof.
  induction l as [|s rest IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; cbn [firstn nth].
  - cbv [total_arg_bytes_nat]. cbn [firstn fold_right].
    rewrite firstn_O. cbn [fold_right]. lia.
  - rewrite !total_arg_bytes_cons. cbn [length] in Hk.
    rewrite (IH k ltac:(lia)). lia.
Qed.

Lemma bsb_len_lower : forall inp mbase ph entry (sp : word) draw,
  (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
     (in_argv inp) (in_envp inp) (in_execfn inp)
   + total_arg_bytes_nat (in_argv inp) + 8
   <= length (entry_stack_image inp mbase ph entry sp draw))%nat.
Proof.
  intros inp mbase ph entry sp draw.
  unfold entry_stack_image. rewrite length_build_stack_bytes.
  unfold cat_string_off, launch_string_bytes.
  cbn [launch_auxv la_rseq].
  rewrite !length_flatten_strings. lia.
Qed.

(* [comment removed for export] *)
Lemma bsb_word_k : forall inp mbase ph entry (sp : word) draw k m,
  (k < length (in_argv inp))%nat ->
  (m <= length (nth k (in_argv inp) []))%nat ->
  exists pre post,
    entry_stack_image inp mbase ph entry sp draw = pre ++ post
    /\ length pre = (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                       (in_argv inp) (in_envp inp) (in_execfn inp)
                     + total_arg_bytes_nat (firstn k (in_argv inp)) + m)%nat
    /\ (8 <= length post)%nat.
Proof.
  intros inp mbase ph entry sp draw k m Hk Hm.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk)
    as [pre0 [post0 [E Hlen0]]].
  pose proof (bsb_len_lower inp mbase ph entry sp draw) as Hlow.
  pose proof (total_arg_bytes_firstn_le (S k) (in_argv inp)) as Hmono.
  pose proof (total_arg_bytes_firstn_S (in_argv inp) k Hk) as Hstep.
  set (s1 := (nth k (in_argv inp) [] ++ [Z_to_bv 8 0])) in *.
  assert (Hs1 : length s1 = (length (nth k (in_argv inp) []) + 1)%nat)
    by (unfold s1; rewrite length_app; cbn [length]; lia).
  assert (Hpost0 : (8 <= length post0)%nat).
  { assert (Hl : length (entry_stack_image inp mbase ph entry sp draw)
                 = (length pre0 + length s1 + length post0)%nat)
      by (rewrite E, !length_app; lia).
    lia. }
  exists (pre0 ++ firstn m s1), (skipn m s1 ++ post0).
  split; [|split].
  - rewrite E, <- !app_assoc. f_equal.
    rewrite app_assoc, firstn_skipn. reflexivity.
  - rewrite length_app, Hlen0, firstn_length_le by lia. lia.
  - rewrite length_app, length_skipn. lia.
Qed.

Lemma read_word_stack : forall v segs inp mbase ph entry (sp brk : word) draw k m,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  (m <= length (nth k (in_argv inp) []))%nat ->
  (bv_unsigned sp
   + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)) < 2^64)%Z ->
  exists bs, length bs = 8%nat /\
    rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
        (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k
         + nat_to_word m) 8%nat = Some bs.
Proof.
  intros v segs inp mbase ph entry sp brk draw k m Hlau Hk Hm Hnw.
  destruct (bsb_word_k inp mbase ph entry sp draw k m Hk Hm)
    as [pre [post [E [Hlen Hpost]]]].
  exists (firstn 8 post). split; [apply firstn_length_le; lia|].
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k
           + nat_to_word m)
    with (sp + nat_to_word (length pre)).
  2:{ rewrite Hlen,
        (cat_argv_ptr_offset (ed_top draw) (in_argv inp) (in_envp inp)
           (in_execfn inp) k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlau).
      rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
  apply (read_at_offset_image segs inp mbase ph entry sp draw
           pre (firstn 8 post) (skipn 8 post) 8%nat).
  - rewrite E. f_equal. symmetry. apply firstn_skipn.
  - apply firstn_length_le. lia.
  - exact Hnw.
Qed.

(* [comment removed for export] *)
Lemma word_bytes_nth :
  forall segs (mem : word -> option byte) (ptr : word) (s : list byte) m bs j,
  rdn segs mem (ptr + nat_to_word m) 8%nat = Some bs ->
  (forall i, (i <= length s)%nat ->
     rdn segs mem (ptr + nat_to_word i) 1%nat = Some [byte_at s i]) ->
  (j < 8)%nat -> (m + j <= length s)%nat ->
  nth j bs (Z_to_bv 8 0) = byte_at s (m + j).
Proof.
  intros segs mem ptr s m bs j Hr Hb Hj Hmj.
  pose proof (rdn_nth segs mem 8%nat _ bs j Hr Hj) as H1.
  rewrite nat_to_word_add_merge in H1.
  rewrite (Hb (m + j)%nat Hmj) in H1.
  congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ArgvWord.

  Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable ph : PhdrInfo.
  Variable entry : word.
  Variable sp brk : word.

  (* [comment removed for export] *)
  Variable draw : EntryDraw.

  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp brk mbase draw) inp.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  (* [comment removed for export] *)
  Lemma mstr_sp_lo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. exact Hsp_lo. Qed.

  Lemma mstr_sp_hi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. exact Hsp_hi. Qed.

  Lemma mstr_bsb_nw :
    (bv_unsigned sp
     + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)) < 2^64)%Z.
  Proof.
    pose proof (bsb_bound v inp mbase ph entry sp brk draw Hvl Hlau).
    pose proof mstr_sp_hi. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma argv_ptr_room : forall k, (k < length (in_argv inp))%nat ->
    (bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                    (in_execfn inp) k)
       + Z.of_nat (length (nth k (in_argv inp) [])) + 9
     <= bv_unsigned sp
        + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)))%Z.
  Proof.
    intros k Hk.
    pose proof mstr_sp_lo. pose proof mstr_sp_hi.
    pose proof mstr_bsb_nw as Hnw.
    pose proof (bsb_len_lower inp mbase ph entry sp draw) as Hlow.
    pose proof (total_arg_bytes_firstn_le (S k) (in_argv inp)) as Hmono.
    pose proof (total_arg_bytes_firstn_S (in_argv inp) k Hk) as Hstep.
    assert (Hptr : cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                     (in_execfn inp) k
      = sp + nat_to_word (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                            (in_argv inp) (in_envp inp) (in_execfn inp)
                          + total_arg_bytes_nat (firstn k (in_argv inp)))).
    { rewrite (cat_argv_ptr_offset (ed_top draw) (in_argv inp) (in_envp inp)
                 (in_execfn inp) k Hk),
              (cat_string_base_offset v inp mbase sp brk draw Hlau).
      rewrite nat_to_word_add_merge. reflexivity. }
    rewrite Hptr, word_add_nat, u_Z2bv by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mstr_argv_ptr_bounds : forall k, (k < length (in_argv inp))%nat ->
    (bv_unsigned sp
     <= bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                       (in_execfn inp) k))%Z /\
    (bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                    (in_execfn inp) k)
       + Z.of_nat (length (nth k (in_argv inp) [])) + 1 < 2^64)%Z.
  Proof.
    intros k Hk. exact (argv_ptr_bounds v inp mbase sp brk draw k Hlau Hk).
  Qed.

  (* [comment removed for export] *)
  Lemma argv_word_readable : forall k m,
    (k < length (in_argv inp))%nat ->
    (m <= length (nth k (in_argv inp) []))%nat ->
    exists bs, length bs = 8%nat /\
      rdn segs (wrap_mem inp mbase ph entry sp draw)
          (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k
           + nat_to_word m) 8%nat = Some bs.
  Proof.
    intros k m Hk Hm.
    pose proof mstr_sp_lo. pose proof mstr_sp_hi.
    destruct (mstr_argv_ptr_bounds k Hk) as [Hge Hup].
    pose proof (argv_ptr_room k Hk) as Hroom.
    pose proof mstr_bsb_nw as Hnw.
    pose proof (u64_range (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                             (in_execfn inp) k)).
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                                (in_execfn inp) k + nat_to_word m)
                 = (bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp)
                                   (in_envp inp) (in_execfn inp) k) + Z.of_nat m)%Z)
      by (rewrite word_add_nat; apply u_Z2bv; lia).
    destruct (read_word_stack v segs inp mbase ph entry sp brk draw k m
                Hlau Hk Hm Hnw) as [bs [Hl Hr]].
    exists bs. split; [exact Hl|].
    rewrite rdn_wrap_stack_above by (rewrite Hu; lia).
    exact Hr.
  Qed.

End ArgvWord.
End MuslStrlen.

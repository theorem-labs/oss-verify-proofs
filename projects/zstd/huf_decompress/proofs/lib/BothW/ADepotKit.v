(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (8 recorded proofs replaced by written proofs (wr_at_app, rw_cells_app, bytes_eq_of_unsigned and 5 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ADepotKit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic3and01K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib4Init5Logic3notK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib7Classes9Morphisms?eq_proper_proxyC59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib7Classes9Morphisms:respectfulC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc59OSSVerify5KrLib5BothW9ADepotKit9wr_at_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveI59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_ReflexiveI47Corelib4Init9Datatypes3nat00C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef3mapI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib5BothW9ADepotKitDbytes_eq_of_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z=shiftr_shiftrC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c59OSSVerify5KrLib5BothW9ADepotKitAZ_to_le_bytes_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ADepotKit?le8_small_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rc59OSSVerify5KrLib5BothW9ADepotKitCrw_cells_recell_midC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma rw_cells_recell_mid : forall segs m A pre mid post mid',
  rw_cells segs m A (pre ++ mid ++ post) -> cells_wf mid' ->
  map bv_unsigned (cells_bytes mid') = map bv_unsigned (cells_bytes mid) ->
  rw_cells segs m A (pre ++ mid' ++ post).
Proof.
  intros segs m A pre mid post mid' RW WF E.
  apply bytes_eq_of_unsigned in E.
  destruct RW as [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W23]. apply cells_wf_app in W23. destruct W23 as [W2 W3].
  assert (SZ : cells_size mid' = cells_size mid).
  { rewrite <- (cells_bytes_length mid' WF), <- (cells_bytes_length mid W2), E. reflexivity. }
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; assumption.
  - rewrite !cells_bytes_app in *. rewrite E. exact Hb.
  - rewrite !cells_size_app in *. rewrite SZ. exact Hw.
Qed.

Lemma Z_to_le_bytes_add : forall a b z, Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
Proof.
  induction a as [|a IH]; intros b z; cbn [Z_to_le_bytes Nat.add app].
  - rewrite Z.shiftr_0_r. reflexivity.
  - f_equal. rewrite IH. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma le8_small_split : forall v, (0 <= v < 2^32)%Z -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
  intros v Hv. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia.
  change 8%nat with (4 + 4)%nat at 1. rewrite Z_to_le_bytes_add. f_equal.
  change (8 * Z.of_nat 4)%Z with 32%Z. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_C8_C4C4 : forall segs m A pre post v,
  rw_cells segs m A (pre ++ C8 (Z_to_bv 64 v) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells segs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post).
Proof.
  intros segs m A pre post v H Hv.
  change (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) with (pre ++ [C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 0)] ++ post).
  eapply rw_cells_recell_mid with (mid := [C8 (Z_to_bv 64 v)]); [exact H | cbv; repeat split |].
  cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (le8_small_split v Hv). reflexivity.
Qed.
Lemma rw_cells_C4C4_C8 : forall segs m A pre post v,
  rw_cells segs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells segs m A (pre ++ C8 (Z_to_bv 64 v) :: post).
Proof.
  intros segs m A pre post v H Hv.
  change (pre ++ C8 (Z_to_bv 64 v) :: post) with (pre ++ [C8 (Z_to_bv 64 v)] ++ post).
  eapply rw_cells_recell_mid with (mid := [C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 0)]); [exact H | cbv; repeat split |].
  cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (le8_small_split v Hv). reflexivity.
Qed.
End CANSEC1.

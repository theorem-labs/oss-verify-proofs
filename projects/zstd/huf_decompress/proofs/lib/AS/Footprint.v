(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (6 recorded proofs replaced by written proofs (rg_disj_sym, covers_mono, covers_nowrap and 3 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Footprint () := "c59OSSVerify5KrLib2AS9Footprint7rg_disjC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9Footprint5rg_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9Footprint5rg_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01i59OSSVerify5KrLib2AS9Footprint6region00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib2AS9Footprint6coversC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib2AS9Footprint5rg_wfC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07I47Corelib4Init5Logic4True00c59OSSVerify5KrLib2AS9Footprint7heap_rgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9Footprint;covers_monoC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record region : Type := Rg { rg_lo : Z; rg_hi : Z }.

Definition rg_wf (r : region) : Prop :=
  0 <= rg_lo r /\ rg_lo r <= rg_hi r /\ rg_hi r <= 2 ^ 64.

(* [comment removed for export] *)
Definition covers (r : region) (a : word) (n : nat) : Prop :=
  rg_lo r <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= rg_hi r.

Definition rg_disj (r1 r2 : region) : Prop :=
  rg_hi r1 <= rg_lo r2 \/ rg_hi r2 <= rg_lo r1.

Lemma rg_disj_sym : forall r1 r2, rg_disj r1 r2 -> rg_disj r2 r1.
Proof. intros r1 r2 [H|H]; [right|left]; exact H. Qed.

(* [comment removed for export] *)
Lemma covers_mono : forall r r' a n,
  covers r a n -> rg_lo r' <= rg_lo r -> rg_hi r <= rg_hi r' -> covers r' a n.
Proof. intros r r' a n [H1 H2] Hl Hh. split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma covers_nowrap : forall r a n,
  rg_wf r -> covers r a n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64.
Proof. intros r a n (_ & _ & Hhi) (_ & H). lia. Qed.

(* [comment removed for export] *)
Lemma covers_disj : forall r1 r2 a1 n1 a2 n2,
  rg_disj r1 r2 -> covers r1 a1 n1 -> covers r2 a2 n2 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof. intros r1 r2 a1 n1 a2 n2 [H|H] [H1 H2] [H3 H4]; [left|right]; lia. Qed.

(* [comment removed for export] *)
Lemma covers_same_disj : forall r a1 n1 a2 n2,
  covers r a1 n1 -> covers r a2 n2 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_rg (sp : word) (below above : Z) : region :=
  Rg (bv_unsigned sp - below) (bv_unsigned sp + above).

(* [comment removed for export] *)
Definition seg_rg (lo hi : Z) : region := Rg lo hi.

(* [comment removed for export] *)
Definition heap_rg (base : word) (cur : Z) : region :=
  Rg (bv_unsigned base) (bv_unsigned base + cur).

Lemma heap_rg_bump : forall base cur cur' a n,
  cur <= cur' -> covers (heap_rg base cur) a n -> covers (heap_rg base cur') a n.
Proof.
  intros base cur cur' a n Hle H.
  apply (covers_mono (heap_rg base cur)); [exact H | cbn; lia | cbn; lia].
Qed.

(* [comment removed for export] *)
Definition layout_wf (rs : list region) : Prop :=
  Forall rg_wf rs /\
  forall i j, (i < j)%nat -> (j < length rs)%nat ->
              rg_disj (nth i rs (Rg 0 0)) (nth j rs (Rg 0 0)).

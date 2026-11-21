(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (6 recorded proofs replaced by written proofs (qsz_0, qsz_eq0, qsz_nz and 3 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import ABase.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AQConst () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2eq00c59OSSVerify5KrLib5BothW7AQConst3qszC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z01C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic9False_indI47Corelib4Init9Datatypes4bool00C56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib5BothW7AQConst6qsz_nzC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2ex00K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2ex01".
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition AQUAR_Q : Z := 0xb6f70.               (* [comment removed for export] *)
Definition AQ_MAX : Z := 0xb6fb0.                (* [comment removed for export] *)
Definition AQ_MIN : Z := 0xb6fb8.                (* [comment removed for export] *)
Definition AQ_MAXC : Z := 0xb6fc0.               (* [comment removed for export] *)
Definition AQ_MUTEX : Z := 0xb7008.              (* [comment removed for export] *)
Definition AQ_GCACHE : Z := 0xb7010.             (* [comment removed for export] *)
Definition aq_tcache (L : alayout) : Z := al_t L + 80.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AIA_BASE : Z := 0xbb500.              (* [comment removed for export] *)
Definition AIA_SIZE : Z := 0x81030.               (* [comment removed for export] *)
Definition AIA_MAP1 : Z := 0xbb508.              (* [comment removed for export] *)
Definition AIA_MAP1_LEN : Z := 0x40000.
Definition AIA_FLAG : Z := 0x149d88.              (* [comment removed for export] *)
Definition AFHOOK : Z := 0x14bdc8.                (* [comment removed for export] *)
End CANSEC1.

(* [comment removed for export] *)
Definition qsz (lst : Z) : Z := if lst =? 0 then 8 else 8192.
Arguments qsz : simpl never.
Lemma qsz_0 : qsz 0 = 8.
Proof. reflexivity. Qed.
Lemma qsz_eq0 : forall lst, lst = 0 -> qsz lst = 8.
Proof. intros lst ->. reflexivity. Qed.
Lemma qsz_nz : forall lst, lst <> 0 -> qsz lst = 8192.
Proof. intros lst H. unfold qsz. destruct (Z.eqb_spec lst 0); [contradiction| reflexivity]. Qed.
Lemma qsz_pos : forall lst, 0 < lst -> qsz lst = 8192.
Proof. intros lst H. apply qsz_nz. lia. Qed.
Lemma qsz_bound : forall lst, 8 <= qsz lst <= 8192.
Proof. intros lst. unfold qsz. destruct (lst =? 0); lia. Qed.
(* [comment removed for export] *)
Lemma qsz_int : forall lst, 0 <= lst -> lst < 18446744073709551616 ->
  exists z, 0 <= z <= 1 /\ qsz lst = 8 + 8184 * z /\ z <= lst /\ lst <= 18446744073709551616 * z.
Proof.
  intros lst H0 H1. unfold qsz. destruct (Z.eqb_spec lst 0) as [E|NE]; [exists 0| exists 1]; lia.
Qed.

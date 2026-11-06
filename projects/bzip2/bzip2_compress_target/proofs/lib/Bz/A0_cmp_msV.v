(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortM CmpMem BzCLemmasMs CmpMsKit AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Record amenv := AME {
  am_P : Z;      (* [comment removed for export] *)
  am_qP : Z;     (* [comment removed for export] *)
  am_FB : Z;     (* [comment removed for export] *)
  am_SLO : Z; am_SHI : Z; am_SD : Z;      (* [comment removed for export] *)
  am_RO : Z; am_BD : Z; am_CS : Z; am_CE : Z   (* [comment removed for export] *)
}.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition amenv_ok (X : msenv) (Y : amenv) : Prop :=
  let usp := bv_unsigned (me_sp X) in
  me_lo X + 4096 <= am_P Y /\ am_P Y + 544 <= usp /\ usp <= am_P Y + 576 /\ am_P Y = 32 * am_qP Y /\
  0x61e000 <= am_FB Y /\ am_FB Y + 5216 <= CEILm /\
  am_SLO Y = am_FB Y + 32 /\ am_SHI Y = am_FB Y + 496 /\ am_SD Y = am_FB Y + 960 /\
  am_RO Y = am_FB Y + 1424 /\ am_BD Y = am_FB Y + 2576 /\ am_CS Y = am_FB Y + 2896 /\ am_CE Y = am_FB Y + 4048 /\
  0x61e000 <= me_E X /\ 0x61e000 <= me_A1 X /\ 0x61e000 <= me_A2 X /\ 0x61e000 <= me_FT X.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition amenv_sep (X : msenv) (Y : amenv) : Prop :=
  apartm (me_E X) 55768 (am_FB Y) 5216 /\ apartm (me_A1 X) ARR1_SIZE (am_FB Y) 5216 /\
  apartm (me_A2 X) ARR2_SIZE (am_FB Y) 5216 /\ apartm (me_FT X) 262148 (am_FB Y) 5216.

(* [comment removed for export] *)
Definition amenv_sepx (X : msenv) (Y : amenv) : Prop :=
  (apartm (me_A1 X) ARR1_SIZE (am_SLO Y) 400 /\ apartm (me_A1 X) ARR1_SIZE (am_SHI Y) 400 /\ apartm (me_A1 X) ARR1_SIZE (am_SD Y) 400 /\
   apartm (me_A1 X) ARR1_SIZE (am_RO Y) 1024 /\ apartm (me_A1 X) ARR1_SIZE (am_BD Y) 256 /\
   apartm (me_A1 X) ARR1_SIZE (am_CS Y) 1024 /\ apartm (me_A1 X) ARR1_SIZE (am_CE Y) 1024) /\
  (apartm (me_A2 X) ARR2_SIZE (am_SLO Y) 400 /\ apartm (me_A2 X) ARR2_SIZE (am_SHI Y) 400 /\ apartm (me_A2 X) ARR2_SIZE (am_SD Y) 400 /\
   apartm (me_A2 X) ARR2_SIZE (am_RO Y) 1024 /\ apartm (me_A2 X) ARR2_SIZE (am_BD Y) 256 /\
   apartm (me_A2 X) ARR2_SIZE (am_CS Y) 1024 /\ apartm (me_A2 X) ARR2_SIZE (am_CE Y) 1024) /\
  (apartm (me_FT X) 262148 (am_SLO Y) 400 /\ apartm (me_FT X) 262148 (am_SHI Y) 400 /\ apartm (me_FT X) 262148 (am_SD Y) 400 /\
   apartm (me_FT X) 262148 (am_RO Y) 1024 /\ apartm (me_FT X) 262148 (am_BD Y) 256 /\
   apartm (me_FT X) 262148 (am_CS Y) 1024 /\ apartm (me_FT X) 262148 (am_CE Y) 1024) /\
  (apartm (me_E X) 55768 (am_SLO Y) 400 /\ apartm (me_E X) 55768 (am_SHI Y) 400 /\ apartm (me_E X) 55768 (am_SD Y) 400 /\
   apartm (me_E X) 55768 (am_RO Y) 1024 /\ apartm (me_E X) 55768 (am_BD Y) 256 /\
   apartm (me_E X) 55768 (am_CS Y) 1024 /\ apartm (me_E X) 55768 (am_CE Y) 1024).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma amsx_1_SLO : forall X Y, amenv_sepx X Y -> me_A1 X + ARR1_SIZE <= am_SLO Y \/ am_SLO Y + 400 <= me_A1 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_1_SHI : forall X Y, amenv_sepx X Y -> me_A1 X + ARR1_SIZE <= am_SHI Y \/ am_SHI Y + 400 <= me_A1 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_1_SD : forall X Y, amenv_sepx X Y -> me_A1 X + ARR1_SIZE <= am_SD Y \/ am_SD Y + 400 <= me_A1 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_1_RO : forall X Y, amenv_sepx X Y -> me_A1 X + ARR1_SIZE <= am_RO Y \/ am_RO Y + 1024 <= me_A1 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_1_BD : forall X Y, amenv_sepx X Y -> me_A1 X + ARR1_SIZE <= am_BD Y \/ am_BD Y + 256 <= me_A1 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_1_CS : forall X Y, amenv_sepx X Y -> me_A1 X + ARR1_SIZE <= am_CS Y \/ am_CS Y + 1024 <= me_A1 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_1_CE : forall X Y, amenv_sepx X Y -> me_A1 X + ARR1_SIZE <= am_CE Y \/ am_CE Y + 1024 <= me_A1 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_2_SLO : forall X Y, amenv_sepx X Y -> me_A2 X + ARR2_SIZE <= am_SLO Y \/ am_SLO Y + 400 <= me_A2 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_2_SHI : forall X Y, amenv_sepx X Y -> me_A2 X + ARR2_SIZE <= am_SHI Y \/ am_SHI Y + 400 <= me_A2 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_2_SD : forall X Y, amenv_sepx X Y -> me_A2 X + ARR2_SIZE <= am_SD Y \/ am_SD Y + 400 <= me_A2 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_2_RO : forall X Y, amenv_sepx X Y -> me_A2 X + ARR2_SIZE <= am_RO Y \/ am_RO Y + 1024 <= me_A2 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_2_BD : forall X Y, amenv_sepx X Y -> me_A2 X + ARR2_SIZE <= am_BD Y \/ am_BD Y + 256 <= me_A2 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_2_CS : forall X Y, amenv_sepx X Y -> me_A2 X + ARR2_SIZE <= am_CS Y \/ am_CS Y + 1024 <= me_A2 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_2_CE : forall X Y, amenv_sepx X Y -> me_A2 X + ARR2_SIZE <= am_CE Y \/ am_CE Y + 1024 <= me_A2 X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_F_SLO : forall X Y, amenv_sepx X Y -> me_FT X + 262148 <= am_SLO Y \/ am_SLO Y + 400 <= me_FT X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_F_SHI : forall X Y, amenv_sepx X Y -> me_FT X + 262148 <= am_SHI Y \/ am_SHI Y + 400 <= me_FT X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_F_SD : forall X Y, amenv_sepx X Y -> me_FT X + 262148 <= am_SD Y \/ am_SD Y + 400 <= me_FT X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_F_RO : forall X Y, amenv_sepx X Y -> me_FT X + 262148 <= am_RO Y \/ am_RO Y + 1024 <= me_FT X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_F_BD : forall X Y, amenv_sepx X Y -> me_FT X + 262148 <= am_BD Y \/ am_BD Y + 256 <= me_FT X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_F_CS : forall X Y, amenv_sepx X Y -> me_FT X + 262148 <= am_CS Y \/ am_CS Y + 1024 <= me_FT X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
Lemma amsx_F_CE : forall X Y, amenv_sepx X Y -> me_FT X + 262148 <= am_CE Y \/ am_CE Y + 1024 <= me_FT X.
Proof. intros X Y H. unfold amenv_sepx, apartm in H. destruct H as ((?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)&(?&?&?&?&?&?&?)). assumption. Qed.
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
Definition acoW (W : list ivl) (m0 : amem) : Prop := forall m : amem, munch W m0 m -> aconsts A0C m.
Lemma acoW_sub : forall W W' (m0 m1 : amem), acoW W m0 -> munch W m0 m1 -> sub_fp W' W -> acoW W' m1.
Proof.
  intros W W' m0 m1 H MU SF m MU'. apply H.
  apply (munch_trans W m0 m1 m MU). exact (munch_weaken W' W m1 m SF MU').
Qed.
Lemma acoW_intro : forall W (m0 : amem), aconsts A0C m0 ->
  disjoint_from W (aci_got_sh A0C) 8 -> disjoint_from W (aci_shvar A0C) 8 -> acoW W m0.
Proof.
  intros W m0 [H1 H2] D1 D2 m MU. split.
  - exact (ro_cells_transport (aci_segs A0C) W m0 m _ _ H1 MU D1).
  - exact (ro_cells_transport (aci_segs A0C) W m0 m _ _ H2 MU D2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record scq := mkSCQ { q216 : word; q224 : word; q232 : word; q240 : word; q256 : word; q264 : word; q272 : word; q288 : word;
                      q320 : word; q328 : word; q336 : word; q344 : word; q352 : word; q360 : word; q368 : word; q376 : word }.
Definition scq_cells (Y : amenv) (s : scq) : list cell :=
  [C8 (q216 s); C8 (q224 s); C8 (q232 s); C8 (q240 s); C8 (Z_to_bv 64 0); C8 (q256 s); C8 (q264 s); C8 (q272 s);
   C8 (Z_to_bv 64 (am_BD Y)); C8 (q288 s); C8 (Z_to_bv 64 (am_SD Y)); C8 (Z_to_bv 64 (am_SHI Y)); C8 (Z_to_bv 64 (am_SLO Y));
   C8 (q320 s); C8 (q328 s); C8 (q336 s); C8 (q344 s); C8 (q352 s); C8 (q360 s); C8 (q368 s); C8 (q376 s)].
Definition scc_cells (X : msenv) : list cell :=
  [C8 (Z_to_bv 64 (me_A2 X + me_qo X)); C8 (Z_to_bv 64 (me_A2 X)); C8 (Z_to_bv 64 (me_n X)); C8 (Z_to_bv 64 (me_A1 X))].

End ACeilS1.

(* [comment removed for export] *)
Ltac box_ors := repeat match goal with H : ?a \/ ?b |- _ => change (a \/ b) with (id (a \/ b)) in H end.

(* [comment removed for export] *)
Ltac amenv_open YOK :=
  let H := fresh "YL" in
  pose proof YOK as H; unfold amenv_ok, CEILm in H; cbv zeta in H;
  cps_destruct H as (?YPl & ?YPh & ?YPg & ?YPa & ?YFl & ?YFh & ?YSLO & ?YSHI & ?YSD & ?YRO & ?YBD & ?YCS & ?YCE & ?YIE & ?YI1 & ?YI2 & ?YIF).

(* [comment removed for export] *)
Ltac open_scq_in H := unfold scq_cells in H; cbn [q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 q352 q360 q368 q376] in H.

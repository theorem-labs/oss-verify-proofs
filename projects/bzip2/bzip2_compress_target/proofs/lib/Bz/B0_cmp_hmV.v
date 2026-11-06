(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCHuff CmpMem CmpHmKit AsanKit.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Record ahenv := AHE {
  ah_P : Z;      (* [comment removed for export] *)
  ah_FB : Z;     (* [comment removed for export] *)
  ah_SHF : Z;    (* [comment removed for export] *)
  ah_HP : Z; ah_WT : Z; ah_PR : Z   (* [comment removed for export] *)
}.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition ahenv_ok (X : hmenv) (Y : ahenv) : Prop :=
  let usp := bv_unsigned (he_sp X) in
  he_lo X <= ah_P Y /\ ah_P Y + 288 <= usp /\ usp <= ah_P Y + 304 /\
  0x62b000 <= ah_FB Y /\ ah_FB Y + 5600 <= CEILh /\
  ah_HP Y = ah_FB Y + 32 /\ ah_WT Y = ah_FB Y + 1200 /\ ah_PR Y = ah_FB Y + 3392 /\
  SH_LO <= ah_SHF Y /\ ah_SHF Y + 700 <= SH_HI.

(* [comment removed for export] *)
Definition ahenv_sep (X : hmenv) (Y : ahenv) : Prop :=
  (he_El X + he_NL X <= ah_FB Y \/ ah_FB Y + 5600 <= he_El X) /\ (he_Ef X + 4 * he_NF X <= ah_FB Y \/ ah_FB Y + 5600 <= he_Ef X).

(* [comment removed for export] *)
Definition ahenv_offsh (X : hmenv) (Y : ahenv) : Prop :=
  (he_El X + he_NL X <= SH_LO \/ SH_HI <= he_El X) /\ (he_Ef X + 4 * he_NF X <= SH_LO \/ SH_HI <= he_Ef X) /\
  (ah_FB Y + 5600 <= SH_LO \/ SH_HI <= ah_FB Y).

(* [comment removed for export] *)
Definition SLb (X : hmenv) (Y : ahenv) (v136 v144 v160 v168 : word) : list cell :=
  [C8 (Z_to_bv 64 (ah_SHF Y)); C8 (Z_to_bv 64 (ah_SHF Y + 424)); C8 (Z_to_bv 64 (ah_SHF Y + 150)); C8 (Z_to_bv 64 (ah_SHF Y + 4));
   C8 (Z_to_bv 64 (ah_FB Y)); C8 (Z_to_bv 64 (ah_FB Y)); C8 (Z_to_bv 64 (he_A X)); C8 (Z_to_bv 64 2060); C8 (Z_to_bv 64 (ah_WT Y + 4));
   C8 (Z_to_bv 64 (he_A X)); C8 (Z_to_bv 64 (he_A X)); C8 (Z_to_bv 64 (he_A X + 1)); C8 (Z_to_bv 64 17); C8 (Z_to_bv 64 (he_El X + he_lb X - 1));
   C8 v136; C8 v144; C8 (Z_to_bv 64 (he_El X + he_lb X)); C8 v160; C8 v168; C8 (Z_to_bv 64 (ah_FB Y))].

(* [comment removed for export] *)
Definition ahenv_sepx (X : hmenv) (Y : ahenv) : Prop :=
  (ah_HP Y + 1040 <= ah_WT Y \/ ah_WT Y + 2064 <= ah_HP Y) /\ (ah_HP Y + 1040 <= ah_PR Y \/ ah_PR Y + 2064 <= ah_HP Y) /\
  (ah_WT Y + 2064 <= ah_PR Y \/ ah_PR Y + 2064 <= ah_WT Y) /\
  (he_El X + he_NL X <= ah_HP Y \/ ah_HP Y + 1040 <= he_El X) /\ (he_El X + he_NL X <= ah_WT Y \/ ah_WT Y + 2064 <= he_El X) /\
  (he_El X + he_NL X <= ah_PR Y \/ ah_PR Y + 2064 <= he_El X) /\
  (he_Ef X + 4 * he_NF X <= ah_HP Y \/ ah_HP Y + 1040 <= he_Ef X) /\ (he_Ef X + 4 * he_NF X <= ah_WT Y \/ ah_WT Y + 2064 <= he_Ef X) /\
  (he_Ef X + 4 * he_NF X <= ah_PR Y \/ ah_PR Y + 2064 <= he_Ef X) /\
  ah_HP Y + 1040 <= ah_P Y /\ ah_WT Y + 2064 <= ah_P Y /\ ah_PR Y + 2064 <= ah_P Y /\
  he_El X + he_NL X <= ah_P Y /\ he_Ef X + 4 * he_NF X <= ah_P Y.

Lemma ahenv_sepx_of : forall X Y, hmenv_ok X -> ahenv_ok X Y -> ahenv_sep X Y -> ahenv_sepx X Y.
Proof.
  intros X Y XOK YOK YSEP.
  unfold hmenv_ok, CEILh in XOK. cbv zeta in XOK. unfold ahenv_ok, CEILh, SH_LO, SH_HI in YOK. cbv zeta in YOK.
  unfold ahenv_sep in YSEP. unfold ahenv_sepx.
  destruct XOK as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _). destruct YOK as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  destruct YSEP as (S1 & S2).
  repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.

(* [comment removed for export] *)
Ltac ahenv_open YOK :=
  let H := fresh "YL" in
  pose proof YOK as H; unfold ahenv_ok, CEILh, SH_LO, SH_HI in H; cbv zeta in H;
  cps_destruct H as (?YPl & ?YPh & ?YPa & ?YFl & ?YFh & ?YHP & ?YWT & ?YPR & ?YSl & ?YSh).

(* [comment removed for export] *)
Ltac ah_box H := lazymatch type of H with ?a \/ ?b => change (a \/ b) with (id (a \/ b)) in H end.
Ltac ahenv_sepx_open YSX :=
  let H := fresh "YSXL" in
  pose proof YSX as H; unfold ahenv_sepx in H;
  let SHW := fresh "SHW" in let SHP := fresh "SHP" in let SWP := fresh "SWP" in let SLH := fresh "SLH" in let SLW := fresh "SLW" in
  let SLP := fresh "SLP" in let SFH := fresh "SFH" in let SFW := fresh "SFW" in let SFP := fresh "SFP" in
  cps_destruct H as (SHW & SHP & SWP & SLH & SLW & SLP & SFH & SFW & SFP & ?YHf & ?YWf & ?YPf & ?YLf & ?YFf);
  ah_box SHW; ah_box SHP; ah_box SWP; ah_box SLH; ah_box SLW; ah_box SLP; ah_box SFH; ah_box SFW; ah_box SFP.

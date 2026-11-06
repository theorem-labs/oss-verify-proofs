(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortF CmpMem BzCLemmasFs CmpFsKit0 AsanKit.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Record afenv := AFE {
  ae_P : Z;      (* [comment removed for export] *)
  ae_FB : Z;     (* [comment removed for export] *)
  ae_SHF : Z;    (* [comment removed for export] *)
  ae_SLO : Z; ae_SHI : Z; ae_FCP : Z   (* [comment removed for export] *)
}.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition afenv_ok (X : fsenv) (Y : afenv) : Prop :=
  let usp := bv_unsigned (fe_sp X) in
  fe_lo X <= ae_P Y /\ ae_P Y + 1376 <= usp /\
  0x61e000 <= ae_FB Y /\ ae_FB Y + 2112 <= CEILv /\
  ae_SLO Y = ae_FB Y + 32 /\ ae_SHI Y = ae_FB Y + 496 /\ ae_FCP Y = ae_FB Y + 960 /\
  SH_LO <= ae_SHF Y /\ ae_SHF Y + 264 <= SH_HI.

(* [comment removed for export] *)
Definition afenv_sep (X : fsenv) (Y : afenv) : Prop :=
  apartv (fe_A1 X) ARR1_SIZE (ae_FB Y) 2112 /\ apartv (fe_A2 X) ARR2_SIZE (ae_FB Y) 2112 /\ apartv (fe_FT X) 262148 (ae_FB Y) 2112.

(* [comment removed for export] *)
Definition afenv_offsh (X : fsenv) (Y : afenv) : Prop :=
  (fe_A1 X + ARR1_SIZE <= SH_LO \/ SH_HI <= fe_A1 X) /\ (fe_A2 X + ARR2_SIZE <= SH_LO \/ SH_HI <= fe_A2 X) /\
  (fe_FT X + 262148 <= SH_LO \/ SH_HI <= fe_FT X) /\ (ae_FB Y + 2112 <= SH_LO \/ SH_HI <= ae_FB Y).

(* [comment removed for export] *)
Definition frdW (segs : list Segment) (W : list ivl) (m0 : amem) (A : Z) (cs : list cell) : Prop :=
  forall m : amem, munch W m0 m -> ro_cells segs m A cs.

Lemma frdW_intro : forall segs W (m0 : amem) A cs,
  rw_cells segs m0 A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> frdW segs W m0 A cs.
Proof. intros segs W m0 A cs [H _] D m MU. exact (ro_cells_transport segs W m0 m A cs H MU D). Qed.

Lemma frdW_sub : forall segs W W' (m0 m1 : amem) A cs,
  frdW segs W m0 A cs -> munch W m0 m1 -> sub_fp W' W -> frdW segs W' m1 A cs.
Proof.
  intros segs W W' m0 m1 A cs H MU SF m MU'. apply H.
  apply (munch_trans W m0 m1 m MU). exact (munch_weaken W' W m1 m SF MU').
Qed.

(* [comment removed for export] *)
Lemma frdW_cell : forall segs W (m0 : amem) A cs k c,
  frdW segs W m0 A cs -> cell_at cs k = Some c -> frdW segs W m0 (A + Z.of_nat k) [c].
Proof.
  intros segs W m0 A cs k c H Hc m MU. specialize (H m MU). destruct H as [Hwf Hb].
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. destruct Hb as [Hb _].
  split; [cbn; tauto|]. cbn [cells_bytes]. rewrite app_nil_r. exact Hb.
Qed.

Lemma frdW_cell_at : forall segs W (m0 : amem) A cs k c A',
  frdW segs W m0 A cs -> cell_at cs k = Some c -> A' = A + Z.of_nat k -> frdW segs W m0 A' [c].
Proof. intros segs W m0 A cs k c A' H Hc ->. exact (frdW_cell segs W m0 A cs k c H Hc). Qed.

(* [comment removed for export] *)
Definition SCq (X : fsenv) (Y : afenv) (lq nnd : Z) (v144 : word) (rr : Z) (v160 : word) (Hh : Z) (v176 v200 v208 : word) : list cell :=
  [C8 (Z_to_bv 64 (fe_A1 X + 4)); C8 (Z_to_bv 64 7621); C8 (Z_to_bv 64 (fe_nb X)); C8 (Z_to_bv 64 lq); C8 (Z_to_bv 64 nnd);
   C8 (Z_to_bv 64 (ae_SHF Y)); C8 (Z_to_bv 64 (fe_nb X)); C8 (Z_to_bv 64 0); C8 v144; C8 (Z_to_bv 64 rr); C8 v160; C8 (Z_to_bv 64 Hh);
   C8 v176; C8 (Z_to_bv 64 (ae_SHI Y)); C8 (Z_to_bv 64 (ae_SLO Y)); C8 v200; C8 v208; C8 (Z_to_bv 64 (fe_A1 X - 4))].

(* [comment removed for export] *)
Definition ec_range (ec : zarr) (n : Z) : Prop := forall k, (0 <= k < n -> 0 <= rd32 ec k < n)%Z.

(* [comment removed for export] *)
Definition afenv_sepx (X : fsenv) (Y : afenv) : Prop :=
  apartv (fe_A1 X) ARR1_SIZE (ae_SLO Y) 400 /\ apartv (fe_A1 X) ARR1_SIZE (ae_SHI Y) 400 /\
  apartv (fe_A2 X) ARR2_SIZE (ae_SLO Y) 400 /\ apartv (fe_A2 X) ARR2_SIZE (ae_SHI Y) 400 /\
  apartv (fe_FT X) 262148 (ae_SLO Y) 400 /\ apartv (fe_FT X) 262148 (ae_SHI Y) 400 /\
  apartv (fe_A1 X) ARR1_SIZE (ae_SHF Y) 264 /\ apartv (fe_A2 X) ARR2_SIZE (ae_SHF Y) 264 /\ apartv (fe_FT X) 262148 (ae_SHF Y) 264 /\
  apartv (ae_SLO Y) 400 (ae_SHF Y) 264 /\ apartv (ae_SHI Y) 400 (ae_SHF Y) 264 /\
  ae_SLO Y + 400 <= ae_P Y /\ ae_SHI Y + 400 <= ae_P Y /\ ae_SHF Y + 264 <= ae_P Y /\ SH_HI <= ae_P Y.

Lemma afenv_sepx_of : forall X Y, fsenv_ok X -> afenv_ok X Y -> afenv_sep X Y -> afenv_offsh X Y -> afenv_sepx X Y.
Proof.
  intros X Y XOK YOK YSEP YOFF. pose proof alloc_ceiling_range as ACR.
  unfold fsenv_ok, CEILv in XOK. cbv zeta in XOK. unfold afenv_ok, CEILv, SH_LO, SH_HI in YOK. cbv zeta in YOK.
  unfold afenv_sep, apartv in YSEP. unfold afenv_offsh, SH_LO, SH_HI in YOFF. unfold afenv_sepx, apartv, SH_HI.
  destruct XOK as (? & ? & ? & ? & ? & ? & ? & ? & ? & _). destruct YOK as (? & ? & ? & ? & ? & ? & ? & ? & ?).
  destruct YSEP as (S1 & S2 & S3). destruct YOFF as (O1 & O2 & O3 & O4).
  repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma app_fp_Wt : forall X Y, fsenv_ok X -> afenv_ok X Y -> afenv_offsh X Y ->
  app_fp [(fe_A1 X, fe_A1 X + ARR1_SIZE); (ae_P Y + 104, ae_P Y + 216); (ae_SLO Y, ae_SLO Y + 400); (ae_SHI Y, ae_SHI Y + 400)].
Proof.
  intros X Y XOK YOK YOFF. pose proof alloc_ceiling_range as ACR.
  unfold fsenv_ok, CEILv in XOK. cbv zeta in XOK. unfold afenv_ok, CEILv, SH_LO, SH_HI in YOK. cbv zeta in YOK.
  unfold afenv_offsh, SH_LO, SH_HI in YOFF.
  destruct XOK as (? & ? & ? & ? & ? & ? & ? & ? & ? & _). destruct YOK as (? & ? & ? & ? & ? & ? & ? & ? & ?).
  destruct YOFF as (O1 & O2 & O3 & O4).
  cbn [app_fp]. unfold SH_LO, SH_HI. repeat split; lia.
Qed.

End ACeilS1.

(* [comment removed for export] *)
Ltac box_ors := repeat match goal with H : ?a \/ ?b |- _ => change (a \/ b) with (id (a \/ b)) in H end.

(* [comment removed for export] *)
Lemma sub_fp_nil6 : forall Wq, sub_fp [] Wq.
Proof. intros Wq x _. exact I. Qed.
Lemma outside_not_inside6 : forall Wq x lo n, outside Wq x -> inside Wq lo n -> ~ (lo <= x < lo + n)%Z.
Proof.
  induction Wq as [|[a b] Wq IH]; intros x lo n Ho Hi; cbn in *.
  - destruct Hi.
  - destruct Ho as [H1 H2]. destruct Hi as [Hi|Hi]; [lia|]. eapply IH; eauto.
Qed.
Lemma sub_fp_cons6 : forall lo hi W Wq, inside Wq lo (hi - lo) -> sub_fp W Wq -> sub_fp ((lo, hi) :: W) Wq.
Proof.
  intros lo hi W Wq Hin Hs x Ho. cbn. split.
  - pose proof (outside_not_inside6 Wq x lo (hi - lo) Ho Hin). lia.
  - apply Hs. exact Ho.
Qed.
(* [comment removed for export] *)
Ltac sub_fp_solve := repeat (apply sub_fp_cons6; [ cbn [inside]; lia | ]); apply sub_fp_nil6.

(* [comment removed for export] *)
Ltac afenv_open YOK :=
  let H := fresh "YL" in
  pose proof YOK as H; unfold afenv_ok, CEILv, SH_LO, SH_HI in H; cbv zeta in H;
  cps_destruct H as (?YPl & ?YPh & ?YFl & ?YFh & ?YSLO & ?YSHI & ?YFCP & ?YSl & ?YSh).

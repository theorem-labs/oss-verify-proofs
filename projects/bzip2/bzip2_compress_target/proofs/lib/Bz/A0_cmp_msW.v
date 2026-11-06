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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition amenv_shf (Y : amenv) (SHF : Z) : Prop := sanchor (am_FB Y) SHF /\ SH_LO <= SHF /\ SHF + 652 <= SH_HI.

(* [comment removed for export] *)
Definition amenv_offsh (X : msenv) (Y : amenv) : Prop :=
  (me_A1 X + ARR1_SIZE <= SH_LO \/ SH_HI <= me_A1 X) /\ (me_A2 X + ARR2_SIZE <= SH_LO \/ SH_HI <= me_A2 X) /\
  (me_FT X + 262148 <= SH_LO \/ SH_HI <= me_FT X) /\ (am_FB Y + 5216 <= SH_LO \/ SH_HI <= am_FB Y).

(* [comment removed for export] *)
Definition amenv_shx (X : msenv) (Y : amenv) (SHF : Z) : Prop :=
  (apartm (me_A1 X) ARR1_SIZE SHF 652 /\ apartm (me_A2 X) ARR2_SIZE SHF 652 /\ apartm (me_FT X) 262148 SHF 652) /\
  (apartm (am_SLO Y) 400 SHF 652 /\ apartm (am_SHI Y) 400 SHF 652 /\ apartm (am_SD Y) 400 SHF 652 /\
   apartm (am_RO Y) 1024 SHF 652 /\ apartm (am_BD Y) 256 SHF 652 /\ apartm (am_CS Y) 1024 SHF 652 /\ apartm (am_CE Y) 1024 SHF 652) /\
  SHF + 652 <= am_P Y - 16 /\ SH_HI <= am_P Y - 16 /\ SHF + 652 <= me_lo X /\ SH_HI <= me_lo X.

(* [comment removed for export] *)

Lemma amsh_1 : forall X Y SHF, amenv_shx X Y SHF -> me_A1 X + ARR1_SIZE <= SHF \/ SHF + 652 <= me_A1 X.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_2 : forall X Y SHF, amenv_shx X Y SHF -> me_A2 X + ARR2_SIZE <= SHF \/ SHF + 652 <= me_A2 X.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_F : forall X Y SHF, amenv_shx X Y SHF -> me_FT X + 262148 <= SHF \/ SHF + 652 <= me_FT X.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_SLO : forall X Y SHF, amenv_shx X Y SHF -> am_SLO Y + 400 <= SHF \/ SHF + 652 <= am_SLO Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_SHI : forall X Y SHF, amenv_shx X Y SHF -> am_SHI Y + 400 <= SHF \/ SHF + 652 <= am_SHI Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_SD : forall X Y SHF, amenv_shx X Y SHF -> am_SD Y + 400 <= SHF \/ SHF + 652 <= am_SD Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_RO : forall X Y SHF, amenv_shx X Y SHF -> am_RO Y + 1024 <= SHF \/ SHF + 652 <= am_RO Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_BD : forall X Y SHF, amenv_shx X Y SHF -> am_BD Y + 256 <= SHF \/ SHF + 652 <= am_BD Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_CS : forall X Y SHF, amenv_shx X Y SHF -> am_CS Y + 1024 <= SHF \/ SHF + 652 <= am_CS Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_CE : forall X Y SHF, amenv_shx X Y SHF -> am_CE Y + 1024 <= SHF \/ SHF + 652 <= am_CE Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_P : forall X Y SHF, amenv_shx X Y SHF -> SHF + 652 <= am_P Y - 16 /\ SH_HI <= am_P Y - 16.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). split; assumption. Qed.
Lemma amsh_L : forall X Y SHF, amenv_shx X Y SHF -> SHF + 652 <= me_lo X /\ SH_HI <= me_lo X.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). split; assumption. Qed.

(* [comment removed for export] *)
Record scl := mkSCL { l40 : word; l48 : word; l56 : word; l72 : word; l80 : word; l88 : word; l96 : word }.
Definition scl_cells (X : msenv) (s : scl) : list cell :=
  [C8 (l40 s); C8 (l48 s); C8 (l56 s); C8 (Z_to_bv 64 (me_FT X + 4)); C8 (l72 s); C8 (l80 s); C8 (l88 s); C8 (l96 s)].
(* [comment removed for export] *)
Definition sc0_cells (X : msenv) : list cell :=
  [C8 (Z_to_bv 64 (me_n X - 1)); C8 (Z_to_bv 64 (me_A1 X - 4)); C8 (Z_to_bv 64 65534)].
Definition sck_cells (X : msenv) (Y : amenv) (SHF : Z) : list cell :=
  [C8 (Z_to_bv 64 (me_A1 X + 4)); C8 (Z_to_bv 64 (am_CE Y)); C8 (Z_to_bv 64 (am_CS Y)); C8 (Z_to_bv 64 SHF)].

(* [comment removed for export] *)
Definition mviews (X : msenv) (Y : amenv) (SHF : Z) (W : list ivl) (me : amem) : Prop :=
  (frdW a0segs W me (am_P Y + 384) (scc_cells X) /\ frdW a0segs W me (am_P Y + 152) (sck_cells X Y SHF) /\
   frdW a0segs W me (am_P Y + 16) (sc0_cells X) /\ frdW a0segs W me (am_P Y + 192) [C8 (Z_to_bv 64 18446744073707454463)] /\ acoW W me) /\
  (shzW a0segs W me (me_A1 X) (me_A1 X + ARR1_SIZE) /\ shzW a0segs W me (me_A2 X) (me_A2 X + ARR2_SIZE) /\
   shzW a0segs W me (me_FT X) (me_FT X + 262144) /\ shpW a0segs W me (me_FT X) (me_FT X + 262148) /\
   shpW a0segs W me (am_P Y + 436) (am_P Y + 440) /\ shzW a0segs W me 139040 139096) /\
  (shzW a0segs W me (am_RO Y) (am_RO Y + 1024) /\ shzW a0segs W me (am_BD Y) (am_BD Y + 256) /\
   shzW a0segs W me (am_CS Y) (am_CS Y + 1024) /\ shzW a0segs W me (am_CE Y) (am_CE Y + 1024)).

Lemma mviews_sub : forall X Y SHF W W' (me m1 : amem), mviews X Y SHF W me -> munch W me m1 -> sub_fp W' W -> mviews X Y SHF W' m1.
Proof.
  intros X Y SHF W W' me m1 ((V1 & V2 & V3 & V4 & AC) & (S1 & S2 & S3 & S4 & S5 & S6) & (S7 & S8 & S9 & S10)) MU SF.
  split; [| split].
  - split; [exact (frdW_sub a0segs W W' me m1 _ _ V1 MU SF)|]. split; [exact (frdW_sub a0segs W W' me m1 _ _ V2 MU SF)|].
    split; [exact (frdW_sub a0segs W W' me m1 _ _ V3 MU SF)|]. split; [exact (frdW_sub a0segs W W' me m1 _ _ V4 MU SF)|].
    exact (acoW_sub W W' me m1 AC MU SF).
  - split; [eapply (shzW_sub a0segs); [exact S1| exact MU| exact SF| lia| lia]|].
    split; [eapply (shzW_sub a0segs); [exact S2| exact MU| exact SF| lia| lia]|].
    split; [eapply (shzW_sub a0segs); [exact S3| exact MU| exact SF| lia| lia]|].
    split; [eapply (shpW_sub a0segs); [exact S4| exact MU| exact SF| lia| lia]|].
    split; [eapply (shpW_sub a0segs); [exact S5| exact MU| exact SF| lia| lia]|].
    eapply (shzW_sub a0segs); [exact S6| exact MU| exact SF| lia| lia].
  - split; [eapply (shzW_sub a0segs); [exact S7| exact MU| exact SF| lia| lia]|].
    split; [eapply (shzW_sub a0segs); [exact S8| exact MU| exact SF| lia| lia]|].
    split; [eapply (shzW_sub a0segs); [exact S9| exact MU| exact SF| lia| lia]|].
    eapply (shzW_sub a0segs); [exact S10| exact MU| exact SF| lia| lia].
Qed.

End ACeilS1.

(* [comment removed for export] *)
Ltac amenv_shx_open X Y SHF SHX :=
  pose proof (amsh_1 X Y SHF SHX) as ZS1; pose proof (amsh_2 X Y SHF SHX) as ZS2; pose proof (amsh_F X Y SHF SHX) as ZSF;
  pose proof (amsh_SLO X Y SHF SHX) as ZSLO; pose proof (amsh_SHI X Y SHF SHX) as ZSHI; pose proof (amsh_SD X Y SHF SHX) as ZSD;
  pose proof (amsh_RO X Y SHF SHX) as ZSRO; pose proof (amsh_BD X Y SHF SHX) as ZSBD; pose proof (amsh_CS X Y SHF SHX) as ZSCS;
  pose proof (amsh_CE X Y SHF SHX) as ZSCE;
  let H := fresh "ZSPH" in pose proof (amsh_P X Y SHF SHX) as H; destruct H as [ZSP ZSH]; unfold SH_HI in ZSH;
  let H2 := fresh "ZSPL" in pose proof (amsh_L X Y SHF SHX) as H2; destruct H2 as [ZSL ZSLH]; unfold SH_HI in ZSLH;
  box_ors.

(* [comment removed for export] *)
Ltac open_scl_in H := unfold scl_cells in H; cbn [l40 l48 l56 l72 l80 l88 l96] in H.
(* [comment removed for export] *)
Ltac mviews_open MV :=
  let H := fresh "MVo" in pose proof MV as H; unfold mviews in H;
  destruct H as ((?VCC & ?VCK & ?VC0 & ?VCM & ?ACW) & (?SH1 & ?SH2 & ?SHFz & ?SHFp & ?SHBU & ?SHIN) & (?SHRO & ?SHBD & ?SHCS & ?SHCE)).

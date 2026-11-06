(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortM CmpMem BzCLemmasMs CmpMsKit AsanKit AsanCut AsanCutB0.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_msW.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition mviews (X : msenv) (Y : amenv) (W : list ivl) (me : amem) : Prop :=
  acoW W me /\
  (shzW b0segs W me (me_A1 X) (me_A1 X + ARR1_SIZE) /\ shzW b0segs W me (me_A2 X) (me_A2 X + ARR2_SIZE) /\
   shzW b0segs W me (me_FT X) (me_FT X + 262144) /\ shpW b0segs W me (me_FT X) (me_FT X + 262148) /\
   shpW b0segs W me (am_P Y + 496) (am_P Y + 500) /\ shzW b0segs W me 858336 858392) /\
  (shzW b0segs W me (am_RO Y) (am_RO Y + 1024) /\ shzW b0segs W me (am_BD Y) (am_BD Y + 256) /\
   shzW b0segs W me (am_CS Y) (am_CS Y + 1024) /\ shzW b0segs W me (am_CE Y) (am_CE Y + 1024)).

Lemma mviews_sub : forall X Y W W' (me m1 : amem), mviews X Y W me -> munch W me m1 -> sub_fp W' W -> mviews X Y W' m1.
Proof.
  intros X Y W W' me m1 (AC & (S1 & S2 & S3 & S4 & S5 & S6) & (S7 & S8 & S9 & S10)) MU SF.
  split; [exact (acoW_sub W W' me m1 AC MU SF)|]. split.
  - split; [eapply (shzW_sub b0segs); [exact S1| exact MU| exact SF| lia| lia]|].
    split; [eapply (shzW_sub b0segs); [exact S2| exact MU| exact SF| lia| lia]|].
    split; [eapply (shzW_sub b0segs); [exact S3| exact MU| exact SF| lia| lia]|].
    split; [eapply (shpW_sub b0segs); [exact S4| exact MU| exact SF| lia| lia]|].
    split; [eapply (shpW_sub b0segs); [exact S5| exact MU| exact SF| lia| lia]|].
    eapply (shzW_sub b0segs); [exact S6| exact MU| exact SF| lia| lia].
  - split; [eapply (shzW_sub b0segs); [exact S7| exact MU| exact SF| lia| lia]|].
    split; [eapply (shzW_sub b0segs); [exact S8| exact MU| exact SF| lia| lia]|].
    split; [eapply (shzW_sub b0segs); [exact S9| exact MU| exact SF| lia| lia]|].
    eapply (shzW_sub b0segs); [exact S10| exact MU| exact SF| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma app_fp_WQA : forall X Y SHF, msenv_ok X -> amenv_ok X Y -> amenv_offsh X Y -> amenv_shx X Y SHF ->
  app_fp [(me_A1 X, me_A1 X + ARR1_SIZE); (am_P Y, am_P Y + 536); (am_P Y - 32, am_P Y);
          (am_SLO Y, am_SLO Y + 400); (am_SHI Y, am_SHI Y + 400); (am_SD Y, am_SD Y + 400)]%Z.
Proof.
  intros X Y SHF XOK YOK YOFF SHX. pose proof alloc_ceiling_range as ACR.
  pose proof (amsh_P X Y SHF SHX) as [_ PH].
  unfold msenv_ok, CEILm in XOK. cbv zeta in XOK. unfold amenv_ok, CEILm in YOK. cbv zeta in YOK.
  unfold amenv_offsh, SH_LO, SH_HI in YOFF. unfold SH_HI in PH.
  destruct XOK as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _).
  destruct YOK as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _).
  destruct YOFF as (O1 & O2 & O3 & O4).
  cbn [app_fp]. unfold SH_LO, SH_HI. repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition bmfree_at (X : msenv) (Y : amenv) (Q : machine_state -> Prop) (pc : Z) (m : word -> option byte) : Prop :=
  forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  evt b0segs Q (MS (mkR x1 (Z_to_bv 64 (am_P Y)) (me_gp X) (me_tp X) x5 x6 x7 (me_sp X) (Z_to_bv 64 (am_P Y))
                        x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880) x28 x29 x30 x31)
                   (me_F X) (Z_to_bv 64 pc) (me_fc X) None m (seg_rom b0segs)).

End ACeilS1.

(* [comment removed for export] *)
Ltac mviews_open MV :=
  let H := fresh "MVo" in pose proof MV as H; unfold mviews in H;
  destruct H as (?ACW & (?SH1 & ?SH2 & ?SHFz & ?SHFp & ?SHBU & ?SHIN) & (?SHRO & ?SHBD & ?SHCS & ?SHCE)).

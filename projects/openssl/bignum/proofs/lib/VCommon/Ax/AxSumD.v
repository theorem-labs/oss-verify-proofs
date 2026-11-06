(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Cli Require Import CliSpecG.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLin AxVal AxMem AxZZ AxState AxSys AxJoinSound AxSum AxTabs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxModelRel AxSumLibc AxSumStr AxSumMem AxSumStdio AxSumStdio0 AxSumAmc AxSumRip2 AxSumChr AxSumBig AxSumBigMs AxSumMzero AxSumMfill AxSumHole.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

Local Notation "a 'orelse' b" := (match a with Some l => Some l | None => b end) (at level 60, right associativity, only parsing).

Definition asum (T : img_tabs) (segs : list Segment) (LIM : Z) (k : Z) (A : AST) : option (list AST) :=
  if k =? 1 then sum_envp segs A
  else if k =? 2 then sum_prog segs A
  else if k =? 3 then sum_strlen segs A
  else if k =? 4 then sum_rip T segs LIM A orelse sum_rip2 T segs LIM A orelse sum_rip_big T segs LIM A
  else if k =? 5 then sum_memchr T segs A
  else if k =? 6 then sum_memcpy segs LIM A orelse sum_memcpy_big segs LIM A
  else if k =? 7 then sum_memset segs LIM A orelse sum_memset_big segs LIM A
  else if k =? 8 then sum_stdio T segs A orelse sum_stdio0 segs A
  else if k =? 9 then sum_amc T segs LIM A
  else if k =? 10 then sum_mzero segs LIM A orelse sum_mfill segs LIM A
  else if k =? 11 then sum_holes segs A
  else None.

Section D.
Variable T : img_tabs.
Hypothesis HT : tabs_ok T = true.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.
Hypothesis KT_emit : forall ρ o bs, KT ρ (o ++ bs) [] -> t_eq (KT ρ o) (t_emit (W 2 bs) (KT ρ (o ++ bs))).

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem asum_sound (k : Z) (A : AST) (l : list AST) : asum T segs LIM k A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  unfold asum.
  destruct (k =? 1); [exact (sum_envp_sound segs cfg LIM fs0 KT A l)|].
  destruct (k =? 2); [exact (sum_prog_sound segs cfg LIM fs0 KT Hlow A l)|].
  destruct (k =? 3); [exact (sum_strlen_sound segs cfg LIM fs0 KT A l)|].
  destruct (k =? 4).
  { destruct (sum_rip T segs LIM A) as [l0|] eqn:E1; [intros H; injection H as <-; exact (sum_rip_sound T HT segs cfg LIM fs0 KT Hlow A l0 E1)|].
    destruct (sum_rip2 T segs LIM A) as [l0|] eqn:E2; [intros H; injection H as <-; exact (sum_rip2_sound T HT segs cfg LIM fs0 KT Hlow A l0 E2)|].
    exact (sum_rip_big_sound T HT segs cfg LIM fs0 KT Hlow A l). }
  destruct (k =? 5); [exact (sum_memchr_sound T HT segs cfg LIM fs0 KT Hlow A l)|].
  destruct (k =? 6).
  { destruct (sum_memcpy segs LIM A) as [l0|] eqn:E1; [intros H; injection H as <-; exact (sum_memcpy_sound segs cfg LIM fs0 KT Hlow A l0 E1)|].
    exact (sum_memcpy_big_sound segs cfg LIM fs0 KT Hlow A l). }
  destruct (k =? 7).
  { destruct (sum_memset segs LIM A) as [l0|] eqn:E1; [intros H; injection H as <-; exact (sum_memset_sound segs cfg LIM fs0 KT Hlow A l0 E1)|].
    first [exact (sum_memset_big_sound segs cfg LIM fs0 KT Hlow A l) | exact (sum_memset_big_sound segs cfg LIM fs0 KT A l)]. }
  destruct (k =? 8).
  { destruct (sum_stdio T segs A) as [l0|] eqn:E1; [intros H; injection H as <-; exact (sum_stdio_sound T HT segs cfg LIM fs0 KT Hlow KT_emit A l0 E1)|].
    exact (sum_stdio0_sound segs cfg LIM fs0 KT Hlow A l). }
  destruct (k =? 9); [exact (sum_amc_sound T HT segs cfg LIM fs0 KT Hlow A l)|].
  destruct (k =? 10).
  { destruct (sum_mzero segs LIM A) as [l0|] eqn:E1; [intros H; injection H as <-; exact (sum_mzero_sound segs cfg LIM fs0 KT Hlow A l0 E1)|].
    exact (sum_mfill_sound segs cfg LIM fs0 KT Hlow A l). }
  destruct (k =? 11); [first [exact (sum_holes_sound segs cfg LIM fs0 KT A l) | exact (sum_holes_sound segs cfg LIM fs0 KT Hlow A l)]|].
  discriminate.
Qed.

End D.

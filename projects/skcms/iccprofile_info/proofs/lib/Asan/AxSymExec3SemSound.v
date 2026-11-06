(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AxSymExec3C.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AX2. Import AX2S. Import AX2B. Import AX2C.
Section WithFP1. Context {FP : PropExec.FPState}.
Lemma side_above_sem : forall segs E M fk b1 k1 n1 c m,
  know_ok segs E M fk -> side_aboveB (mkbc fk) b1 k1 n1 c m = true -> side_testB (mkbc fk) b1 k1 n1 c m = (false, false).
Proof.
  intros segs E M fk b1 k1 n1 c m HK H. unfold side_aboveB in H. apply quick_ge0B_ge0 in H. rewrite lin_ge0B_eqf in H.
  pose proof (lin_ge0_sound segs E M fk _ _ HK H) as G. cbn [xt_den] in G.
  rewrite side_testB_eq. f_equal.
  - destruct n1 as [z1| | | | | | |]; try reflexivity.
    destruct (sub_itvB (mkbc fk) b1 k1 (zlit64 z1) c m) eqn:S; [|reflexivity]. exfalso.
    rewrite sub_itvB_eqf in S. destruct (sub_itv_sound segs E M fk b1 k1 (zlit64 z1) c m HK S) as [A B].
    unfold estart, elenZ in *. cbn [a_base a_off edenot] in *. rewrite u_lit64, <- zlit64_eq in G. lia.
  - destruct (sub_itv_xB (mkbc fk) b1 k1 n1 c m) eqn:S; [|reflexivity]. exfalso.
    rewrite sub_itv_xB_eqf in S. destruct (sub_itv_x_sound segs E M fk b1 k1 n1 c m HK S) as [A B].
    unfold estart, elenZ in *. cbn [a_base a_off] in *. lia.
Qed.
Lemma side_testS_sem : forall segs E M fk b1 k1 n1 c m,
  know_ok segs E M fk -> side_testS (mkbc fk) b1 k1 n1 c m = side_testB (mkbc fk) b1 k1 n1 c m.
Proof.
  intros segs E M fk b1 k1 n1 c m HK. unfold side_testS. destruct (side_aboveB (mkbc fk) b1 k1 n1 c m) eqn:A; [|reflexivity].
  symmetry. exact (side_above_sem segs E M fk b1 k1 n1 c m HK A).
Qed.
Lemma carryKS_sem : forall segs E M fk log kn hints,
  know_ok segs E M fk -> carryKS (mkbc fk) log kn hints = carryKM (mkbc fk) log kn hints.
Proof. intros segs E M fk log kn hints HK. apply carryKS_pt. intros. exact (side_testS_sem segs E M fk _ _ _ _ _ HK). Qed.
End WithFP1.


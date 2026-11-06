(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import NodesCfg DecodeCfg NodesCfgA.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad STree Malloc MallocCtrl Prog ProgDetIface ProgDetLogic ProgDetNodes ProgDetMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma tpath_a_stepR : forall {R} (t : itree node R) mo tr r mo',
  tsafe nstep_a nsafe t mo -> minv mo -> m_halted mo = None ->
  tpath nstep_a t mo tr r mo' -> tpath (stepR None) t mo tr r mo'.
Proof.
  intros R t. induction t as [r0|n k IH|v k IH]; intros mo tr r mo' Hs Hmi Hh Hp; cbn in *; [exact Hp| |].
  2:{ destruct Hp as (a & Hv & Hp). exists a. split; [exact Hv|]. exact (IH a mo tr r mo' (Hs a Hv) Hmi Hh Hp). }
  destruct Hs as [Hsafe Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & ->).
  destruct (DecodeCfg.minv_preserved n mo rsp mo1 evs Hmi Hh Hsafe (nstep_a_c _ _ _ _ _ Hst)) as [Hh1 Hmi1].
  exists rsp, mo1, evs, tr'. split.
  - split; [exact (conj Hsafe (conj (nstep_a_noerr _ _ _ _ _ Hst) (conj Hmi Hh)))|]. split; [exact (nstep_a_c _ _ _ _ _ Hst)| exact I].
  - split; [exact (IH rsp mo1 tr' r mo' (Hk _ _ _ Hst) Hmi1 Hh1 Hp)| reflexivity].
Qed.

Section WithCeiling. Context {CE__ : Ceiling}.

Lemma raw_malloc_some_path : forall n s mo tr r s' mo', size_overflows n = false ->
  tsafe nstep_a nsafe (raw_malloc n s) mo -> minv mo -> m_halted mo = None ->
  tpath nstep_a (raw_malloc n s) mo tr (Ok (r, s')) mo' -> r <> None.
Proof.
  intros n s mo tr r s' mo' Hn Hs Hmi Hh Hp.
  assert (HK : fstable (fun _ _ _ => True)) by (intros ? ? ? ? ? _ _ _ _; exact I).
  pose proof (raw_malloc_E None (fun _ => True) n (fun _ _ _ => True) HK Hn s mo [] I) as W.
  pose proof (twfE_tpath None (fun _ => True) _ mo [] _ tr (r, s') mo' W (tpath_a_stepR _ mo tr _ mo' Hs Hmi Hh Hp)) as [_ Hne].
  exact Hne.
Qed.

End WithCeiling.

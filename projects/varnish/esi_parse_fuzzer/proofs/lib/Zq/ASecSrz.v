(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import RelSpec PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import Divembc SpinAlg Ledger Hull Restrict Lazyiq4 EvtAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Grow.
  Variables (A0 A1 : hull) (W : list (Z * Z)).
  (* [comment removed for export] *)
  Hypothesis SUB : forall iv, In iv A0 -> In iv A1.
  (* [comment removed for export] *)
  Hypothesis NEW : forall x, in_hullb A1 x = true -> in_hullb A0 x = false -> ~ outside W x.

  Lemma hidc_grow : forall a, hidc A1 a = true -> hidc A0 a = true.
  Proof.
    intros a H. unfold hidc in *. apply negb_true_iff in H. apply negb_true_iff.
    destruct (in_hullb A0 (bv_unsigned a)) eqn:E; [| reflexivity]. exfalso.
    apply in_hullb_true in E as (lo & hi & Hin & R). rewrite (in_hullb_intro A1 _ lo hi (SUB _ Hin) R) in H. discriminate.
  Qed.

  (* [comment removed for export] *)
  Variables (full m0' mz : word -> option byte).
  Hypothesis CLEAN : forall a, hidc A0 a = true -> m0' a = None.
  Hypothesis MZ : forall a, outside W (bv_unsigned a) -> mz a = munrestrict (hidc A0) full m0' a.

  Lemma restrict_grow_munch : munch W m0' (mrestrict (hidc A1) mz).
  Proof.
    intros x Hout. unfold mrestrict. destruct (hidc A1 x) eqn:V1.
    - symmetry. apply CLEAN. apply hidc_grow. exact V1.
    - rewrite (MZ x Hout). unfold munrestrict. destruct (hidc A0 x) eqn:V0; [| reflexivity].
      exfalso. apply (NEW (bv_unsigned x)); [| | exact Hout]; unfold hidc in *.
      + apply negb_false_iff in V1. exact V1.
      + apply negb_true_iff in V0. exact V0.
  Qed.

  (* [comment removed for export] *)
  Hypothesis PRESV : forall a, hidc A0 a = false -> m0' a <> None -> mz a <> None.

  Lemma restrict_grow_wmono : forall segs, wmono segs m0' (mrestrict (hidc A1) mz).
  Proof.
    intros segs x Hx. unfold wview in *. unfold mrestrict.
    destruct (m0' x) as [b|] eqn:M0.
    - (* [comment removed for export] *)
      assert (V0 : hidc A0 x = false) by (destruct (hidc A0 x) eqn:V0; [rewrite (CLEAN x V0) in M0; discriminate| reflexivity]).
      assert (V1 : hidc A1 x = false) by (destruct (hidc A1 x) eqn:V1; [pose proof (hidc_grow x V1); congruence| reflexivity]).
      rewrite V1. destruct (mz x) as [b'|] eqn:MZx; [discriminate|]. exfalso. apply (PRESV x V0); congruence.
    - (* [comment removed for export] *)
      destruct (hidc A1 x); [exact Hx|]. destruct (mz x); [discriminate| exact Hx].
  Qed.
End Grow.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac Lept_kit Lept_iface.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac shbr_inv8 :=
  lazymatch goal with
  | K : shk ?m ?b ?X, ACC : acc asegs ?m ?a ?n |- evt _ _ (MS _ _ (if _ then _ else _) _ _ ?m _) =>
      let OK := fresh "SHOK" in
      assert (OK : sh_ok b (X + 8 - 1)) by (apply (shk_ok m a n X 8 b ACC K); lia);
      apply sh_ok_8 in OK; [ | lia ]; rewrite ?OK; brT; clear K OK
  end.

Section CKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma accok_below : forall Σ m a n, ART RT Σ m -> accok (rt_live RT Σ) (rt_frames RT Σ) m a n ->
  a + n <= rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
  intros Σ m a n HA [(p & k & Hin & H1 & H2)|(f & k & Hin & H1 & H2 & _)].
  - pose proof (af_live_range RT AF Σ m p k HA Hin) as (_ & R & _). lia.
  - pose proof (af_frames_range RT AF Σ m f k HA Hin) as (_ & R & _). lia.
Qed.
End CKit.

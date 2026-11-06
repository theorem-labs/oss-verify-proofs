(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image Ceiling.
From OSSVerify.Proofs.openssl.bignum.lib Require Import TopLevel Obligations ProofBase TopLevelA TopE.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog ModelInv Canon CanonNoKill ProgDetIface ProgDet ProgNoEnomem.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition Tc (inp : ProcInput) : list event -> Prop := canonT (argv_Z (in_argv inp)) (in_fs inp).

Lemma Tc_nokill : T_nokill Tc.
Proof. intros inp tr sig fs H. exact (canonT_nokill _ _ tr sig fs H). Qed.



Theorem S_side : forall tsegs tpc tph, S3s_stmt tsegs tpc tph ->
  side_canon ncfg Tc (mkImage tsegs tpc tph) target_alloc_limit.
Proof. intros tsegs tpc tph HS en inp He Hi. exact (T_canon tsegs tpc tph HS en inp He Hi). Qed.

Section Bases.


  Section Ubsan.



  End Ubsan.

  Section AsanFamily.
    Variables (tsegs : list Segment) (tpc : N) (tph : PhdrInfo).
    Hypothesis HS : S3s_stmt tsegs tpc tph.


  End AsanFamily.
End Bases.

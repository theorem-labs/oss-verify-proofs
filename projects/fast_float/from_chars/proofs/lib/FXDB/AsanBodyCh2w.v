(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcFam AcSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2 AcFam3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSubst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import FxMchr AsanPNodes AsanBNodes AsanTailCh AsanBodyCh AsanBodyCh2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BodyCh2w.
Context {N : Type}.
Notation MC := (@mchain N).
Variable A1n : anode -> MC -> MC.
Variable A2n : anode2 -> MC -> MC.
Variable A3n : anode3 -> MC -> MC.
Variable BNn : bnode -> MC -> MC.
Variable VIA : positive.
Variable VCT : positive.
Variable OFF : nat.
(* [comment removed for export] *)
Definition DIAW (pc : Z) (k : MC) : MC := MJoin (MSegK 40 (planFR 3) (KCons pc 0 MEnd KNil)) pc k.
(* [comment removed for export] *)
Definition KTAILF_W (jb ib : nat) (k : MC) : MC :=
  BNn (BSplitW32 ib 6128) (BNn (BPlaceW jb)
    (SEGFR 0x82908 (A1n NUnw) (SEGFR 0x81f7c (A1n NPut) (DIAW 0xd4904 (KMSFR A1n (SEGFR 0x43e20 (KENQ A2n A3n BNn VCT) (SEGFR2 0x8fcb8 k))))))).
Definition TAILF_EW (jb ib : nat) (k : MC) : MC := A3n NCacheAdd (KFREEN A1n BNn VIA (KTAILF_W jb ib k)).
Definition TAILF_PW (jb ib : nat) (k : MC) : MC := A3n NCacheAdd (KFREEO_PJ A1n A2n A3n BNn VIA VCT OFF (KTAILF_W jb ib k)).
Definition TAILF_LW (jl : nat) (qu mp : positive) (jb ib : nat) (k : MC) : MC := A3n NCacheAdd (KFREEO_LJ A1n A2n A3n BNn VIA VCT OFF jl qu mp (KTAILF_W jb ib k)).
End BodyCh2w.
(* [comment removed for export] *)

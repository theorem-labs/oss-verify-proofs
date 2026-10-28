(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit AW_LargeAlloc1 AS_Refill1 AllocTacX AllocPerfKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Lemma rrenv_transport_img : forall tp TSD CTX TH sb ARI m m' W,
    AS_Refill1.RENV tp TSD CTX TH sb ARI m -> munch W m m' -> wmono asegs m m' -> out_img W ->
    65536 <= bv_unsigned tp + -88 -> bv_unsigned tp + -88 + 8 <= 12599296 ->
    65536 <= TSD -> TSD + 8 <= 12599296 ->
    disjoint_from W (CTX + 152) 8 ->
    AS_Refill1.RENV tp TSD CTX TH sb ARI m'.
  Proof.
    intros tp TSD CTX TH sb ARI m m' W E MU WM HW T1 T2 D1 D2 DC.
    apply (AS_Refill1.renv_transport tp TSD CTX TH sb ARI m m' W E MU WM); try exact DC; apply (out_img_disjoint W _ _ HW); lia.
  Qed.
End HCW.

(* [comment removed for export] *)
Ltac rrenv_img_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with AS_Refill1.RENV ?tp ?TSD ?CTX ?TH ?sb ?ARI m =>
      assert (E' : AS_Refill1.RENV tp TSD CTX TH sb ARI m');
      [ apply (rrenv_transport_img tp TSD CTX TH sb ARI m m' W E MU WM);
        [ out_img_tac ltac:(cbn [fst snd]; region_decide) | .. ]; cbn [disjoint_from]; region_decide | ]
    end end.

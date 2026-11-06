(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit AW_MallocBase AW_LargeAlloc1 AW_PoisonRemap1 AllocPerfKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Lemma ienv_transport_img : forall tp TSD CTX TH sb TOP BOT m m' W,
    IENV tp TSD CTX TH sb TOP BOT m -> munch W m m' -> wmono asegs m m' -> out_img W ->
    65536 <= bv_unsigned tp + -88 -> bv_unsigned tp + 32 + 4 <= 12386304 ->
    65536 <= TSD -> TSD + 8 <= 12386304 ->
    disjoint_from W (CTX + 152) 8 -> disjoint_from W TH 8 -> disjoint_from W (CTX + 8) 4 -> disjoint_from W (TH + 8) 16 -> disjoint_from W (TH + 40) 1 ->
    IENV tp TSD CTX TH sb TOP BOT m'.
  Proof.
    intros tp TSD CTX TH sb TOP BOT m m' W E MU WM HW T1 T2 D1 D2 C1 C2 C3 C4 C5.
    destruct E; constructor;
      (eapply rw_cells_transport; [eassumption | exact MU | exact WM | ]);
      unfold AGOT_VALS; cbn [cells_size csize length map repeat Nat.add Nat.mul];
      first [ assumption | apply (out_img_disjoint W _ _ HW); lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma ienv_transport_split : forall tp TSD CTX TH sb TOP BOT m m' W Wo Wi,
    IENV tp TSD CTX TH sb TOP BOT m -> munch W m m' -> wmono asegs m m' ->
    (forall a n, disjoint_from Wo a n -> disjoint_from Wi a n -> disjoint_from W a n) ->
    out_img Wo ->
    65536 <= bv_unsigned tp + -88 -> bv_unsigned tp + 32 + 4 <= 12386304 -> 65536 <= TSD -> TSD + 8 <= 12386304 ->
    disjoint_from Wi (bv_unsigned tp + -88) 8 -> disjoint_from Wi TSD 8 -> disjoint_from Wi (bv_unsigned tp + 32) 4 ->
    disjoint_from Wi 6777632 8 -> disjoint_from Wi 0x5af310 8 -> disjoint_from Wi 6782872 1 -> disjoint_from Wi 7312672 3 ->
    disjoint_from Wi 6777628 1 -> disjoint_from Wi 5957240 120 -> disjoint_from Wi 6779576 8 -> disjoint_from Wi 6782880 24 ->
    disjoint_from Wi 7376480 8 -> disjoint_from Wi 5970128 8 -> disjoint_from Wi 6769380 12 -> disjoint_from Wi 6769421 1 ->
    disjoint_from Wi 7376256 80 -> disjoint_from Wi 6765688 8 -> disjoint_from Wi 6769272 16 ->
    disjoint_from Wi 0x677fbc 4 -> disjoint_from Wi 0x706d60 8 -> disjoint_from Wi (0x708de8 + 34) 1 ->
    disjoint_from W (CTX + 152) 8 -> disjoint_from W TH 8 -> disjoint_from W (CTX + 8) 4 -> disjoint_from W (TH + 8) 16 -> disjoint_from W (TH + 40) 1 ->
    IENV tp TSD CTX TH sb TOP BOT m'.
  Proof.
    intros tp TSD CTX TH sb TOP BOT m m' W Wo Wi E MU WM SPL HW T1 T2 D1 D2.
    intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20 I21 C1 C2 C3 C4 C5.
    destruct E; constructor;
      (eapply rw_cells_transport; [eassumption | exact MU | exact WM | ]);
      unfold AGOT_VALS; cbn [cells_size csize length map repeat Nat.add Nat.mul];
      first [ assumption | apply SPL; [ apply (out_img_disjoint Wo _ _ HW); lia | assumption ] ].
  Qed.
End HCW.

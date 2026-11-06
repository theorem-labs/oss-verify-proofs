(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.GcFlush11.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 ArtMem EbtLeaf ArtRuns ArtRunsMem EbtCls EbtCellEx
     ArtBridge EbrInv EbrInvMalloc EbtLift EbrWrapKit EbrFsInv EbrFsInvLaws EbrIfaceLaws EbrInvFrame EbrIfaceFrame EbrWrapC EbrWrapVis EbrWrapC2 EbrWrapRng EbrWrapStrlen EbrWrapMemI
     EbrIcptLaws PeBImgGap.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section IL.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

Theorem art_law_img_gap : PMBGAP.rt_img_gap HI.
Proof.
  intros LB FF LK cr A M V (G & _ & FS & _ & _ & CLI & _).
  destruct (fsinv_cs _ _ _ _ _ FS) as (_ & _ & _ & _ & _ & _ & SH & _).
  destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & IMGSH & _).
  unfold PMBGAP.GAP_LO, PMBGAP.GAP_HI, PMBGAP.GAPB_LO, PMBGAP.GAPB_HI, PMBGAP.IMG_LO, PMBGAP.IMG_HI. split; [split| split].
  - intros x Hx. apply SH. right; right; right; left. exact Hx.
  - apply (art_shadow_allowed_sub A 0x10000 (0x69c000 - 0x10000)); [exact IMGSH | lia | lia | lia].
  - intros x Hx. apply SH. right; left. exact Hx.
  - exact IMGSH.
Qed.
End IL.

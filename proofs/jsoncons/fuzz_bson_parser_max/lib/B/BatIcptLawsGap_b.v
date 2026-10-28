(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.GcFlush11.  (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatCellEx_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b BatInvFrame_b BatIfaceFrame_b BatWrapC_b BatWrapVis_b BatWrapC2_b BatWrapRng_b BatWrapStrlen_b BatWrapMemI_b
     BatIcptLaws_b PnAImgGap_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section IL.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

Theorem art_law_img_gap : PMAGAP.rt_img_gap HI.
Proof.
  intros LB FF LK cr A M V (G & _ & FS & _ & _ & CLI & _).
  destruct (fsinv_cs _ _ _ _ _ FS) as (_ & _ & _ & _ & _ & _ & SH & _).
  destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & IMGSH & _).
  unfold PMAGAP.GAP_LO, PMAGAP.GAP_HI. split.
  - intros x Hx. apply SH. right; right; right; left. exact Hx.
  - apply (art_shadow_allowed_sub A 0x10000 (0x696000 - 0x10000)); [exact IMGSH | lia | lia | lia].
Qed.
End IL.

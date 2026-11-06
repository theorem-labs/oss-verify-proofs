(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.GcFlush11.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA ArtMem JatLeaf ArtRuns ArtRunsMem JatCls JatCellEx
ArtBridge JatInv JatInvMalloc JatLift JatWrapKit JatFsInv JatFsInvLaws JatIfaceLaws JatInvFrame JatIfaceFrame JatWrapC JatWrapVis JatWrapC2 JatWrapRng JatWrapStrlen JatWrapMemI
JatIcptLaws PmAImgGap.
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
- intros x Hx. apply SH. right; right; left. exact Hx.
- apply (art_shadow_allowed_sub A 0x10000 (0x691000 - 0x10000)); [exact IMGSH | lia | lia | lia].
Qed.
End IL.

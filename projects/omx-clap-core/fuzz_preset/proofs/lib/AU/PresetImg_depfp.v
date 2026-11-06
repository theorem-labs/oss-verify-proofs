(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_depfp.v (commit 4d286b2e618d, file sha256 9e7745374ae4) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 2 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 5 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, row img-depfp-B of the internal file REPLY-IMG-ROWS.md, for a Theorem Labs lane's cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row; a closed computation at reply's image B, fuzz_reply.asan-ubsan, pin
   10ffb5f9202a).  Reuse search: proof-index dep_fp_img footprint_DZONE dep_fp_a_cgif (index v5, 2026-10-30
   04:38Z): dep_fp_img is only the layer's Definition (YGcfInstDepot.v:165); footprint_DZONE exists at cgif, decode,
   preset and state, none at fuzz_reply; no discharge of the row at any reply image.

   The row is the cf layer's [dep_fp_img B DZ] (YGcfInstDepot.v:165-166 at c0780f715a3c, lane F1):
     forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a -> DZ ly a,
   for the two zones the layer uses, the Allocate zone ImgBaseAG.ag_dzone and the Deallocate zone ImgBaseDG.dg_dzone
   (cgif's discharges: YGcfInstF1Wcgif.v:82 dep_fp_a_cgif / :89 dep_fp_d_cgif, both by AGix.footprint_DZONE).  Reply
   has not taken YGcfInstDepot.v yet, so each Lemma states that Definition's body VERBATIM at reply's image-B instances
   (ImgBase.AImg_cgif, B/AGif2cgif.v:24; ImgBaseAG.AGImg_cgif, B/AGif0cgif.v:116, ag_dzone := AGis.DZONE;
   ImgBaseDG.DImg_cgif, B/DGif0cgif.v:30, dg_dzone := DGgi.DZONE), for every B with the image's symbol facts
   (im_syms = TfibSyms); a consumer closes the layer's row with `exact (dep_fp_a_B B TS)` once the layer is on reply.
   No Definition of the layer is copied here.

   The computation: StackDepotPut's write set (B/CLdepot.v:48-50) is the depot [as_depot B, + d_map1 + 8 * 32768), the
   nodes block, the store block and the store [as_store B, + 64).  At image B as_depot B = TFIB_DEPOT = 0x188518 and
   as_store B = TFIB_STORE = 0x17d5c8 (values B/YF0m.v:17; fields ts_depot / ts_store B/YF0m.v:864-865), d_map1 =
   4 * 2 ^ 20 + 16 (Reusable/YG0f.v:225),
   so the depot ends at 0x5c8528 and the store at 0x178548, both inside the zone's static part [0x17d5c8, 0x5cdd50)
   (B/AGis.v:231-232 and B/DGgi.v:515-516, the same text); the nodes and store blocks are the zone's other two
   disjuncts verbatim. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGis DGgi AGif0cgif DGif0cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot.
Open Scope Z_scope.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The write set of StackDepotPut at image B lies in [0x17d5c8, 0x5cdd50) or is the nodes / store block. *)
Lemma depot_footprint_B : forall B ly a, @im_syms AImg_cgif B -> CLdepot.depot_footprint B ly a ->
  (0x17d5c8 <= a < 0x5cdd50) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
  (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros B ly a TS FP. change (TfibSyms B) in TS.
unfold CLdepot.depot_footprint in FP. rewrite (ts_depot B TS), (ts_store B TS) in FP.
change d_map1 with 4194320 in FP. unfold TFIB_DEPOT, TFIB_STORE in FP. lia.
Qed.

(* dep_fp_img B ag_dzone (YGcfInstDepot.v:165-166) at image B. *)
Lemma dep_fp_a_B : forall B, @im_syms AImg_cgif B ->
  forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a ->
  @ImgBaseAG.ag_dzone AImg_cgif AGif0cgif.AGImg_cgif ly a.
Proof.
intros B TS ly a _ _ _ FP. change (AGis.DZONE ly a). unfold AGis.DZONE.
exact (depot_footprint_B B ly a TS FP).
Qed.

(* dep_fp_img B dg_dzone (YGcfInstDepot.v:165-166) at image B. *)
Lemma dep_fp_d_B : forall B, @im_syms AImg_cgif B ->
  forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a ->
  @ImgBaseDG.dg_dzone AImg_cgif DGif0cgif.DImg_cgif ly a.
Proof.
intros B TS ly a _ _ _ FP. change (DGgi.DZONE ly a). unfold DGgi.DZONE.
exact (depot_footprint_B B ly a TS FP).
Qed.

End rows.

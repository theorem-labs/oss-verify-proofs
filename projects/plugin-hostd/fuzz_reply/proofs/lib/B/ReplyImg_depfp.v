(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-depfp-B of REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record), for a Theorem Labs lane's cf layer at
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
   (ImgBase.AImg_reply, B/AGif2reply.v:24; ImgBaseAG.AGImg_reply, B/AGif0reply.v:117, ag_dzone := AGis.DZONE;
   ImgBaseDG.DImg_reply, B/DGif0reply.v:31, dg_dzone := DGgi.DZONE), for every B with the image's symbol facts
   (im_syms = TfibSyms); a consumer closes the layer's row with `exact (dep_fp_a_B B TS)` once the layer is on reply.
   No Definition of the layer is copied here.

   The computation: StackDepotPut's write set (B/CLdepot.v:48-50) is the depot [as_depot B, + d_map1 + 8 * 32768), the
   nodes block, the store block and the store [as_store B, + 64).  At image B as_depot B = TFIB_DEPOT = 0x188518 and
   as_store B = TFIB_STORE = 0x178508 (values B/YF0m.v:17; fields ts_depot / ts_store B/YF0m.v:875-876), d_map1 =
   4 * 2 ^ 20 + 16 (Reusable/YG0f.v:228),
   so the depot ends at 0x5c8528 and the store at 0x178548, both inside the zone's static part [0x178508, 0x5c8c90)
   (B/AGis.v:231-232 and B/DGgi.v:515-516, the same text); the nodes and store blocks are the zone's other two
   disjuncts verbatim. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGis DGgi AGif0reply DGif0reply CLdepot.
Open Scope Z_scope.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The write set of StackDepotPut at image B lies in [0x178508, 0x5c8c90) or is the nodes / store block. *)
Lemma depot_footprint_B : forall B ly a, @im_syms AImg_reply B -> CLdepot.depot_footprint B ly a ->
  (0x178508 <= a < 0x5c8c90) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
  (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros B ly a TS FP. change (TfibSyms B) in TS.
unfold CLdepot.depot_footprint in FP. rewrite (ts_depot B TS), (ts_store B TS) in FP.
change d_map1 with 4194320 in FP. unfold TFIB_DEPOT, TFIB_STORE in FP. lia.
Qed.

(* dep_fp_img B ag_dzone (YGcfInstDepot.v:165-166) at image B. *)
Lemma dep_fp_a_B : forall B, @im_syms AImg_reply B ->
  forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a ->
  @ImgBaseAG.ag_dzone AImg_reply AGif0reply.AGImg_reply ly a.
Proof.
intros B TS ly a _ _ _ FP. change (AGis.DZONE ly a). unfold AGis.DZONE.
exact (depot_footprint_B B ly a TS FP).
Qed.

(* dep_fp_img B dg_dzone (YGcfInstDepot.v:165-166) at image B. *)
Lemma dep_fp_d_B : forall B, @im_syms AImg_reply B ->
  forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a ->
  @ImgBaseDG.dg_dzone AImg_reply DGif0reply.DImg_reply ly a.
Proof.
intros B TS ly a _ _ _ FP. change (DGgi.DZONE ly a). unfold DGgi.DZONE.
exact (depot_footprint_B B ly a TS FP).
Qed.

End rows.

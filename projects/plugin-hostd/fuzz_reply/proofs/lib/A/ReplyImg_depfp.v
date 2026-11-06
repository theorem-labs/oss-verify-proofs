(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30: row img-depfp-A of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record) (CF-UNIT-HYPS.md:41 sha256 77b3f94c95d2; internal record): the cf layer's image
   premise dep_fp_img B DZ (YGcfInstDepot.v:165-167, "what StackDepotPut may write lies in the zone DZ the caller frames
   out") at plugin-hostd/fuzz_reply's image A (asan, pin 42c58610e125), for both zones the layer uses:
   DZ := ag_dzone (AGImg_reply's, = AGis.DZONE) and DZ := dg_dzone (DImg_reply's, = DGgi.DZONE).
   The reply tree does not carry YGcfInstDepot.v, so each theorem states dep_fp_img's text UNFOLDED:
     dep_fp_img B DZ := forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
                        CLdepot.depot_footprint B ly a -> DZ ly a.
   Ported (form and script, no numeral) from preset's A/YGcfInstF1WA.v dep_fp_a_A / dep_fp_d_A
   (a working branch 7700305f42c4) and cgif's YGcfInstF1Wcgif.v:82 / :89 dep_fp_a_cgif / dep_fp_d_cgif
   (a working branch 511c76f79c41), which both apply AGix.footprint_DZONE (cgif AGix.v:162-166); reply A has
   no AGix, so the script is inlined: the footprint's two table ranges are reply A's own TfibSyms values
   (AF0m.v:18 TFIB_DEPOT / TFIB_STORE through ts_depot / ts_store), the nodes and store blocks are DZONE's own arms.
   rule 24: no function proved (kind: image premise over the unit's tables). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply AGif0reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CLdepot.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* StackDepotPut's footprint at reply A lies in the depot zone [TFIB_STORE, TFIB_DEPOT + d_map1 + 8 * 32768) plus the
   nodes and store blocks (AGis.v:230-231 = DGgi.v:514-515). *)
Lemma footprint_DZONE_reply : forall ly a, CLdepot.depot_footprint B ly a ->
  (TFIB_STORE <= a < TFIB_DEPOT + d_map1 + 8 * 32768) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
  (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros ly a FP. unfold CLdepot.depot_footprint in FP. rewrite (ts_depot B TS), (ts_store B TS) in FP.
unfold TFIB_DEPOT, TFIB_STORE, d_map1 in *. lia.
Qed.

(* dep_fp_img B ag_dzone, unfolded (YGcfInstDepot.v:166-167). *)
Theorem dep_fp_a_A : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  CLdepot.depot_footprint B ly a -> ag_dzone ly a.
Proof.
intros ly a _ _ _ FP. destruct (footprint_DZONE_reply ly a FP) as [X|[X|X]]; [left | right; left | right; right].
- unfold TFIB_DEPOT, TFIB_STORE, d_map1 in X. lia.
- exact X.
- exact X.
Qed.

(* dep_fp_img B dg_dzone, unfolded (YGcfInstDepot.v:166-167). *)
Theorem dep_fp_d_A : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  CLdepot.depot_footprint B ly a -> dg_dzone ly a.
Proof.
intros ly a _ _ _ FP. destruct (footprint_DZONE_reply ly a FP) as [X|[X|X]]; [left | right; left | right; right].
- unfold TFIB_DEPOT, TFIB_STORE, d_map1 in X. lia.
- exact X.
- exact X.
Qed.
End a.

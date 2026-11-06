(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-hcw-A of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record); merger ReallocPrimary.CfW).
   rule 24: no function proved (kind: image row; a closed fact over reply's image A, fuzz_reply.asan).
   Reuse search: the row's own cgif discharge, YGcfInstHitcgif.v:95 HCW_cgif (a working branch ee95275bccb), and
   reply's ReplyImg_depkeep.v (a Theorem Labs lane, the constant cells' zone at reply A): no HCW discharge at reply.

   HCW is the cf layer's YGcfInstHit.v:160-162 (commit ee95275bccb):
     forall ly' c j cl', layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
       In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
       ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
   Every name in it is on reply already (ImgBase.AImg at AImg_reply, A/AGif2reply.v; ImgBaseAG.WINT, A/ImgBaseAG.v:123),
   so [hcw_A] states it verbatim at reply's instance and a consumer closes the layer's row with `exact`.
   The proof is HCW_cgif's: the constant cells lie in reply's constant-cell zone AGif0reply.CZONE (A/AGif0reply.v:63),
   by ReplyImg_depkeep.const_cells_zone (cgif's AGix.const_cells_zone at reply's tables); CZONE misses every WINT cell,
   since WINT lies in the thread object at offsets >= 208 (Pv = T + t_cache + 80 * cl), 2768 (the literal
   [T + 2768, T + 2824)), 2912 + 8 * cl (SSLOTv = T + t_stats + 112 + 8 * cl) and 3168 (t_unwinding), all above CZONE's
   thread part [T, T + 80); the image part and the TSD slot are apart from the thread
   object by static_extents' disjointness (indices 2 and 9: T and the image, img_cover), the high shadow part by the
   thread object's in_app (lo_app), and the context map and the D page by static_extents (2 / 6, 2 / 7). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGis ImgBaseAG ReplyImg_depkeep.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* HCW at image A (YGcfInstHit.v:160-162 at reply's instance; cgif: YGcfInstHitcgif.v:95 HCW_cgif). *)
Theorem hcw_A : forall B, @im_syms AImg_reply B ->
  forall ly' c j cl', layout_ok ly' -> @im_img_cover AImg_reply ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
Proof.
intros B TS ly c j cl LY IMG HT Hc Hj Hcl Hw. change (TfibSyms B) in TS. change (img_cover ly) in IMG.
assert (HT' : ly_tsd ly = TFIB_TSD) by (rewrite HT; exact (ts_tsd B TS)).
pose proof (ReplyImg_depkeep.const_cells_zone B ly TS LY IMG HT' c j Hc Hj) as CZ.
set (a := aeval B ly (c_at c) + j) in *. clearbody a.
destruct IMG as [I1 I2].
pose proof (lo_disj ly LY) as HD.
pose proof (AGis.pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl) as DTI.
pose proof (AGis.pairwise_ij _ _ 2 3 _ _ HD eq_refl eq_refl) as DTC.
pose proof (AGis.pairwise_ij _ _ 2 4 _ _ HD eq_refl eq_refl) as DTD.
pose proof (AGis.Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as AT.
unfold zdisjoint in DTI, DTC, DTD. cbn beta in AT. cbn [fst snd] in DTI, DTC, DTD, AT.
unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in Hw. unfold CZONE in CZ.
clear - CZ Hw Hcl DTI DTC DTD AT I1 I2.
unfold in_app, TFIB_TSD, TFIB_IMG_LO, TFIB_IMG_END, kThreadObjSize, t_cache, t_stats, t_unwinding,
  kLowShadowBeg, kHighMemBeg in *.
lia.
Qed.

End d.
